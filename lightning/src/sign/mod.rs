// This file is Copyright its original authors, visible in version control
// history.
//
// This file is licensed under the Apache License, Version 2.0 <LICENSE-APACHE
// or http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your option.
// You may not use this file except in accordance with one or both of these
// licenses.

//! Provides keys to LDK and defines some useful objects describing spendable on-chain outputs.
//!
//! The provided output descriptors follow a custom LDK data format and are currently not fully
//! compatible with Bitcoin Core output descriptors.

use bitcoin::amount::Amount;
use bitcoin::bip32::{ChildNumber, Xpriv, Xpub};
use bitcoin::ecdsa::Signature as EcdsaSignature;
use bitcoin::locktime::absolute::LockTime;
use bitcoin::network::Network;
use bitcoin::opcodes;
use bitcoin::script::{Builder, Script, ScriptBuf};
use bitcoin::sighash;
use bitcoin::sighash::EcdsaSighashType;
use bitcoin::transaction::Version;
use bitcoin::transaction::{Transaction, TxIn, TxOut};

use bitcoin::hashes::sha256::Hash as Sha256;
use bitcoin::hashes::sha256d::Hash as Sha256dHash;
use bitcoin::hashes::{Hash, HashEngine};

use bitcoin::secp256k1::ecdh::SharedSecret;
use bitcoin::secp256k1::ecdsa::{RecoverableSignature, Signature};
use bitcoin::secp256k1::schnorr;
use bitcoin::secp256k1::All;
use bitcoin::secp256k1::{Keypair, PublicKey, Scalar, Secp256k1, SecretKey, Signing};
use bitcoin::{secp256k1, Psbt, Sequence, Txid, WPubkeyHash, Witness};

use lightning_invoice::RawBolt11Invoice;

use crate::chain::transaction::OutPoint;
use crate::crypto::utils::{hkdf_extract_expand_twice, sign, sign_with_aux_rand};
use crate::ln::chan_utils;
use crate::ln::chan_utils::{
	get_countersigner_payment_script, get_revokeable_redeemscript, get_taproot_to_remote_spk,
	make_funding_redeemscript,
	ChannelPublicKeys, ChannelTransactionParameters, ClosingTransaction, CommitmentTransaction,
	HTLCOutputInCommitment, HolderCommitmentTransaction,
};
use crate::ln::channel::ANCHOR_OUTPUT_VALUE_SATOSHI;
use crate::ln::channel_keys::{
	add_public_key_tweak, DelayedPaymentBasepoint, DelayedPaymentKey, HtlcBasepoint, HtlcKey,
	RevocationBasepoint, RevocationKey,
};
use crate::ln::inbound_payment::ExpandedKey;
use crate::ln::msgs::PartialSignatureWithNonce;
use crate::ln::msgs::{UnsignedChannelAnnouncement, UnsignedGossipMessage};
use crate::ln::script::ShutdownScript;
use crate::offers::invoice::UnsignedBolt12Invoice;
use crate::types::features::ChannelTypeFeatures;
use crate::types::payment::PaymentPreimage;
use crate::util::async_poll::AsyncResult;
use crate::util::ser::{ReadableArgs, Writeable};
use crate::util::transaction_utils;

use crate::crypto::chacha20::ChaCha20;
use crate::prelude::*;
use crate::sign::ecdsa::EcdsaChannelSigner;
use crate::sign::taproot::TaprootChannelSigner;
use crate::sync::{Arc, Mutex};
use crate::util::atomic_counter::AtomicCounter;
use core::convert::TryInto;
use core::ops::Deref;
use core::sync::atomic::{AtomicUsize, Ordering};
use musig2::{PartialSignature, PubNonce as PublicNonce};

pub(crate) mod type_resolver;

pub mod ecdsa;
pub mod taproot;
pub mod taproot_signer;
pub mod tx_builder;

pub(crate) const COMPRESSED_PUBLIC_KEY_SIZE: usize = bitcoin::secp256k1::constants::PUBLIC_KEY_SIZE;

pub(crate) const MAX_STANDARD_SIGNATURE_SIZE: usize =
	bitcoin::secp256k1::constants::MAX_SIGNATURE_SIZE;

/// Information about a spendable output to a P2WSH script.
///
/// See [`SpendableOutputDescriptor::DelayedPaymentOutput`] for more details on how to spend this.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct DelayedPaymentOutputDescriptor {
	/// The outpoint which is spendable.
	pub outpoint: OutPoint,
	/// Per commitment point to derive the delayed payment key by key holder.
	pub per_commitment_point: PublicKey,
	/// The `nSequence` value which must be set in the spending input to satisfy the `OP_CSV` in
	/// the witness_script.
	pub to_self_delay: u16,
	/// The output which is referenced by the given outpoint.
	pub output: TxOut,
	/// The revocation point specific to the commitment transaction which was broadcast. Used to
	/// derive the witnessScript for this output.
	pub revocation_pubkey: RevocationKey,
	/// Arbitrary identification information returned by a call to [`ChannelSigner::channel_keys_id`].
	/// This may be useful in re-deriving keys used in the channel to spend the output.
	pub channel_keys_id: [u8; 32],
	/// The value of the channel which this output originated from, possibly indirectly.
	pub channel_value_satoshis: u64,
	/// The channel public keys and other parameters needed to generate a spending transaction or
	/// to provide to a signer.
	///
	/// Added as optional, but always `Some` if the descriptor was produced in v0.0.123 or later.
	pub channel_transaction_parameters: Option<ChannelTransactionParameters>,
}

impl DelayedPaymentOutputDescriptor {
	/// The maximum length a well-formed witness spending one of these should have.
	///
	/// Note: If you have the `grind_signatures` feature enabled, this will be at least 1 byte
	/// shorter.
	pub const MAX_WITNESS_LENGTH: u64 = (1 /* witness items */
		+ 1 /* sig push */
		+ MAX_STANDARD_SIGNATURE_SIZE
		+ 1 /* empty vec push */
		+ 1 /* redeemscript push */
		+ chan_utils::REVOKEABLE_REDEEMSCRIPT_MAX_LENGTH) as u64;

	/// Whether this descriptor's `to_local` output is a simple-taproot (BOLT #995)
	/// P2TR output (swept via a BIP341 script-path spend) rather than a legacy P2WSH
	/// output (swept via an ECDSA witness).
	pub fn is_taproot(&self) -> bool {
		self.channel_transaction_parameters
			.as_ref()
			.map(|p| p.channel_type_features.supports_simple_taproot())
			.unwrap_or(false)
	}

	/// The maximum length a well-formed witness spending this output should have.
	///
	/// For legacy (P2WSH ECDSA) channels this is the static [`Self::MAX_WITNESS_LENGTH`].
	/// For simple-taproot (BOLT #995, M9e) channels the `to_local` is swept via a
	/// BIP341 SCRIPT-path spend of the `to_delay` tapleaf — a HEAVIER witness — and
	/// the exact weight is computed **dynamically** (build-and-measure) by
	/// [`Self::taproot_max_witness_weight`], which needs a `secp` context. Callers that
	/// have a `secp` (e.g. the spendable-output PSBT builder) MUST use
	/// [`Self::taproot_max_witness_weight`] for taproot outputs; this `secp`-less
	/// method falls back to the legacy bound and is only correct for non-taproot
	/// descriptors.
	pub fn max_witness_length(&self) -> u64 {
		Self::MAX_WITNESS_LENGTH
	}

	/// The worst-case serialized weight (witness units) of the witness spending this
	/// `to_local` output.
	///
	/// For legacy channels this returns the static [`Self::MAX_WITNESS_LENGTH`]. For
	/// simple-taproot (BOLT #995, M9e) channels the `to_local` sweep is a BIP341
	/// script-path spend of the `to_delay` tapleaf — `[<64B schnorr sig>, <to_delay
	/// tapleaf>, <control block>]` — whose weight is computed **dynamically** by
	/// BUILDING the real witness (the actual tapleaf script + control block from this
	/// output's `to_local` spend info, with a max-size dummy Schnorr sig) and measuring
	/// it, rather than from a hardcoded constant. Every element is fixed-length (x-only
	/// pubkeys are 32 bytes, the Schnorr sig 64 bytes, the 2-leaf control block 65
	/// bytes) and the `to_self_delay` push uses this descriptor's real delay value, so
	/// the result is an exact, never-underestimating upper bound that stays correct if
	/// the tapleaf script or tree shape ever changes.
	///
	/// The tapleaf/control-block depend only on the output's keys and `to_self_delay`,
	/// not on the (private) delayed-payment key, so the descriptor's `revocation_pubkey`
	/// doubles as the placeholder delayed-payment key for the weight measurement — the
	/// serialized witness length is invariant to which 32-byte x-only key is used.
	pub fn taproot_max_witness_weight<C: secp256k1::Signing + secp256k1::Verification>(
		&self, secp: &Secp256k1<C>,
	) -> Result<u64, ()> {
		if !self.is_taproot() {
			return Ok(Self::MAX_WITNESS_LENGTH);
		}
		// A 64-byte all-zero BIP340 Schnorr signature is a valid-length placeholder;
		// only its serialized length matters for the weight measurement.
		let dummy_sig = schnorr::Signature::from_slice(&[0u8; 64]).map_err(|_| ())?;
		// The delayed-payment key value does not affect the witness length (all x-only
		// pubkeys serialize to 32 bytes); reuse the descriptor's revocation pubkey as a
		// length-equivalent placeholder so this is computable from the descriptor alone.
		let dummy_delayed_key = DelayedPaymentKey(self.revocation_pubkey.to_public_key());
		let leaf = chan_utils::get_taproot_to_local_delay_script(
			self.to_self_delay,
			&dummy_delayed_key,
		);
		let spend_info = chan_utils::taproot_to_local_spend_info(
			secp,
			&self.revocation_pubkey,
			self.to_self_delay,
			&dummy_delayed_key,
		);
		let elem = chan_utils::taproot_schnorr_witness_element(
			&dummy_sig,
			bitcoin::sighash::TapSighashType::Default,
		);
		let witness = chan_utils::build_taproot_script_path_witness(elem, &leaf, &spend_info)
			.map_err(|_| ())?;
		// `witness.size()` is the exact serialized witness for this input. The per-input
		// satisfaction-weight model omits the per-tx BIP141 segwit marker+flag (2 WU),
		// which the conservative P2WSH constants happen to absorb but this exact taproot
		// measurement does not; attribute it here so the estimate stays a safe upper
		// bound.
		Ok(witness.size() as u64 + chan_utils::SEGWIT_MARKER_FLAG_WEIGHT)
	}
}

impl_writeable_tlv_based!(DelayedPaymentOutputDescriptor, {
	(0, outpoint, required),
	(2, per_commitment_point, required),
	(4, to_self_delay, required),
	(6, output, required),
	(8, revocation_pubkey, required),
	(10, channel_keys_id, required),
	(12, channel_value_satoshis, required),
	(13, channel_transaction_parameters, (option: ReadableArgs, Some(channel_value_satoshis.0.unwrap()))),
});

/// Witness weight for satisfying a P2WPKH spend.
pub(crate) const P2WPKH_WITNESS_WEIGHT: u64 = (1 /* witness items */
	+ 1 /* sig push */
	+ MAX_STANDARD_SIGNATURE_SIZE
	+ 1 /* pubkey push */
	+ COMPRESSED_PUBLIC_KEY_SIZE) as u64;

/// Witness weight for satisfying a P2TR key-path spend.
pub(crate) const P2TR_KEY_PATH_WITNESS_WEIGHT: u64 = (1 /* witness items */
	+ 1 /* sig push */
	+ bitcoin::secp256k1::constants::SCHNORR_SIGNATURE_SIZE)
	as u64;

/// If a [`KeysManager`] is built with [`KeysManager::new`] with `v2_remote_key_derivation` set
/// (and for all channels after they've been spliced), the script which we receive funds to on-chain
/// when our counterparty force-closes a channel is one of this many possible derivation paths.
///
/// Keeping this limited allows for scanning the chain to find lost funds if our state is destroyed,
/// while this being more than a handful provides some privacy by not constantly reusing the same
/// scripts on-chain across channels.
// Note that this MUST remain below the maximum BIP 32 derivation paths (2^31)
pub const STATIC_PAYMENT_KEY_COUNT: u16 = 1000;

/// Information about a spendable output to our "payment key".
///
/// See [`SpendableOutputDescriptor::StaticPaymentOutput`] for more details on how to spend this.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct StaticPaymentOutputDescriptor {
	/// The outpoint which is spendable.
	pub outpoint: OutPoint,
	/// The output which is referenced by the given outpoint.
	pub output: TxOut,
	/// Arbitrary identification information returned by a call to [`ChannelSigner::channel_keys_id`].
	/// This may be useful in re-deriving keys used in the channel to spend the output.
	pub channel_keys_id: [u8; 32],
	/// The value of the channel which this transactions spends.
	pub channel_value_satoshis: u64,
	/// The necessary channel parameters that need to be provided to the signer.
	///
	/// Added as optional, but always `Some` if the descriptor was produced in v0.0.117 or later.
	pub channel_transaction_parameters: Option<ChannelTransactionParameters>,
}

impl StaticPaymentOutputDescriptor {
	/// Returns the `witness_script` of the spendable output.
	///
	/// Note that this will only return `Some` for [`StaticPaymentOutputDescriptor`]s that
	/// originated from an anchor outputs channel, as they take the form of a P2WSH script.
	pub fn witness_script(&self) -> Option<ScriptBuf> {
		self.channel_transaction_parameters.as_ref().and_then(|channel_params| {
			if channel_params.channel_type_features.supports_anchors_zero_fee_htlc_tx() {
				let payment_point = channel_params.holder_pubkeys.payment_point;
				Some(chan_utils::get_to_countersigner_keyed_anchor_redeemscript(&payment_point))
			} else {
				None
			}
		})
	}

	/// The maximum length a well-formed witness spending one of these should have.
	///
	/// Note: If you have the `grind_signatures` feature enabled, this will be at least 1 byte
	/// shorter.
	///
	/// This is the legacy P2WSH/P2WPKH estimate; for simple-taproot (BOLT #995) channels the
	/// `to_remote` is a BIP341 script-path spend of a 1-CSV tapleaf — a HEAVIER witness — whose
	/// exact weight is computed **dynamically** by [`Self::taproot_max_witness_weight`] (which
	/// needs a `secp` context). Callers that have a `secp` (e.g. the spendable-output PSBT
	/// builder) MUST use [`Self::taproot_max_witness_weight`]; this `secp`-less method
	/// under-counts the taproot case and is only correct for non-taproot descriptors.
	pub fn max_witness_length(&self) -> u64 {
		if self.needs_csv_1_for_spend() {
			let witness_script_weight = 1 /* pubkey push */
				+ COMPRESSED_PUBLIC_KEY_SIZE
				+ 1 /* OP_CHECKSIGVERIFY */
				+ 1 /* OP_1 */
				+ 1 /* OP_CHECKSEQUENCEVERIFY */;
			(1 /* num witness items */
				+ 1 /* sig push */
				+ MAX_STANDARD_SIGNATURE_SIZE
				+ 1 /* witness script push */
				+ witness_script_weight) as u64
		} else {
			P2WPKH_WITNESS_WEIGHT
		}
	}

	/// Whether this descriptor's `to_remote` output is a simple-taproot (BOLT #995) P2TR
	/// output (swept via a BIP341 script-path spend of the 1-CSV tapleaf) rather than a
	/// legacy P2WSH/P2WPKH output.
	pub fn is_taproot(&self) -> bool {
		self.channel_transaction_parameters
			.as_ref()
			.map(|p| p.channel_type_features.supports_simple_taproot())
			.unwrap_or(false)
	}

	/// The worst-case serialized weight (witness units) of the witness spending this
	/// `to_remote` output.
	///
	/// For legacy channels this returns [`Self::max_witness_length`]. For simple-taproot
	/// (BOLT #995, M9e) channels the `to_remote` sweep is a BIP341 script-path spend of the
	/// 1-CSV tapleaf (`<remote> OP_CHECKSIGVERIFY 1 OP_CSV`) — `[<64B schnorr sig>, <tapleaf>,
	/// <control block>]` — which is HEAVIER than the legacy P2WSH/P2WPKH estimate (the legacy
	/// estimate UNDER-counts it). The taproot weight is computed **dynamically** by BUILDING
	/// the real witness (the actual tapleaf script + single-leaf control block from this
	/// output's `to_remote` spend info, with a max-size dummy Schnorr sig) and measuring it,
	/// rather than from a hardcoded constant. Every element is fixed-length, so the result is
	/// an exact, never-underestimating upper bound that stays correct if the tapleaf script or
	/// tree shape ever changes.
	///
	/// The tapleaf/control-block witness length is invariant to the (32-byte x-only) remote
	/// pubkey value, so the channel's `holder_pubkeys.payment_point` is used as the placeholder.
	pub fn taproot_max_witness_weight<C: secp256k1::Signing + secp256k1::Verification>(
		&self, secp: &Secp256k1<C>,
	) -> Result<u64, ()> {
		if !self.is_taproot() {
			return Ok(self.max_witness_length());
		}
		let params = self.channel_transaction_parameters.as_ref().ok_or(())?;
		let remote_pubkey = params.holder_pubkeys.payment_point;
		// A 64-byte all-zero BIP340 Schnorr signature is a valid-length placeholder; only its
		// serialized length matters for the weight measurement.
		let dummy_sig = schnorr::Signature::from_slice(&[0u8; 64]).map_err(|_| ())?;
		let leaf = chan_utils::get_taproot_to_remote_script(&remote_pubkey);
		let spend_info = chan_utils::taproot_to_remote_spend_info(secp, &remote_pubkey);
		let elem = chan_utils::taproot_schnorr_witness_element(
			&dummy_sig,
			bitcoin::sighash::TapSighashType::Default,
		);
		let witness = chan_utils::build_taproot_script_path_witness(elem, &leaf, &spend_info)
			.map_err(|_| ())?;
		// `witness.size()` is the exact serialized witness for this input. The per-input
		// satisfaction-weight model omits the per-tx BIP141 segwit marker+flag (2 WU), which
		// the conservative P2WSH constants happen to absorb but this exact taproot measurement
		// does not; attribute it here so the estimate stays a safe upper bound.
		Ok(witness.size() as u64 + chan_utils::SEGWIT_MARKER_FLAG_WEIGHT)
	}

	/// Returns true if spending this output requires a transaction with a CheckSequenceVerify
	/// value of at least 1.
	pub fn needs_csv_1_for_spend(&self) -> bool {
		let chan_params = self.channel_transaction_parameters.as_ref();
		chan_params.map_or(false, |p| p.channel_type_features.supports_anchors_zero_fee_htlc_tx())
	}
}
impl_writeable_tlv_based!(StaticPaymentOutputDescriptor, {
	(0, outpoint, required),
	(2, output, required),
	(4, channel_keys_id, required),
	(6, channel_value_satoshis, required),
	(7, channel_transaction_parameters, (option: ReadableArgs, Some(channel_value_satoshis.0.unwrap()))),
});

/// Describes the necessary information to spend a spendable output.
///
/// When on-chain outputs are created by LDK (which our counterparty is not able to claim at any
/// point in the future) a [`SpendableOutputs`] event is generated which you must track and be able
/// to spend on-chain. The information needed to do this is provided in this enum, including the
/// outpoint describing which `txid` and output `index` is available, the full output which exists
/// at that `txid`/`index`, and any keys or other information required to sign.
///
/// [`SpendableOutputs`]: crate::events::Event::SpendableOutputs
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum SpendableOutputDescriptor {
	/// An output to a script which was provided via [`SignerProvider`] directly, either from
	/// [`get_destination_script`] or [`get_shutdown_scriptpubkey`], thus you should already
	/// know how to spend it. No secret keys are provided as LDK was never given any key.
	/// These may include outputs from a transaction punishing our counterparty or claiming an HTLC
	/// on-chain using the payment preimage or after it has timed out.
	///
	/// [`get_shutdown_scriptpubkey`]: SignerProvider::get_shutdown_scriptpubkey
	/// [`get_destination_script`]: SignerProvider::get_shutdown_scriptpubkey
	StaticOutput {
		/// The outpoint which is spendable.
		outpoint: OutPoint,
		/// The output which is referenced by the given outpoint.
		output: TxOut,
		/// The `channel_keys_id` for the channel which this output came from.
		///
		/// For channels which were generated on LDK 0.0.119 or later, this is the value which was
		/// passed to the [`SignerProvider::get_destination_script`] call which provided this
		/// output script.
		///
		/// For channels which were generated prior to LDK 0.0.119, no such argument existed,
		/// however this field may still be filled in if such data is available.
		channel_keys_id: Option<[u8; 32]>,
	},
	/// An output to a P2WSH script which can be spent with a single signature after an `OP_CSV`
	/// delay.
	///
	/// The witness in the spending input should be:
	/// ```bitcoin
	/// <BIP 143 signature> <empty vector> (MINIMALIF standard rule) <provided witnessScript>
	/// ```
	///
	/// Note that the `nSequence` field in the spending input must be set to
	/// [`DelayedPaymentOutputDescriptor::to_self_delay`] (which means the transaction is not
	/// broadcastable until at least [`DelayedPaymentOutputDescriptor::to_self_delay`] blocks after
	/// the outpoint confirms, see [BIP
	/// 68](https://github.com/bitcoin/bips/blob/master/bip-0068.mediawiki)). Also note that LDK
	/// won't generate a [`SpendableOutputDescriptor`] until the corresponding block height
	/// is reached.
	///
	/// These are generally the result of a "revocable" output to us, spendable only by us unless
	/// it is an output from an old state which we broadcast (which should never happen).
	///
	/// To derive the delayed payment key which is used to sign this input, you must pass the
	/// holder [`InMemorySigner::delayed_payment_base_key`] (i.e., the private key which
	/// corresponds to the [`ChannelPublicKeys::delayed_payment_basepoint`] in
	/// [`ChannelSigner::pubkeys`]) and the provided
	/// [`DelayedPaymentOutputDescriptor::per_commitment_point`] to
	/// [`chan_utils::derive_private_key`]. The DelayedPaymentKey can be generated without the
	/// secret key using [`DelayedPaymentKey::from_basepoint`] and only the
	/// [`ChannelPublicKeys::delayed_payment_basepoint`] which appears in
	/// [`ChannelSigner::pubkeys`].
	///
	/// To derive the [`DelayedPaymentOutputDescriptor::revocation_pubkey`] provided here (which is
	/// used in the witness script generation), you must pass the counterparty
	/// [`ChannelPublicKeys::revocation_basepoint`] and the provided
	/// [`DelayedPaymentOutputDescriptor::per_commitment_point`] to
	/// [`RevocationKey`].
	///
	/// The witness script which is hashed and included in the output `script_pubkey` may be
	/// regenerated by passing the [`DelayedPaymentOutputDescriptor::revocation_pubkey`] (derived
	/// as explained above), our delayed payment pubkey (derived as explained above), and the
	/// [`DelayedPaymentOutputDescriptor::to_self_delay`] contained here to
	/// [`chan_utils::get_revokeable_redeemscript`].
	DelayedPaymentOutput(DelayedPaymentOutputDescriptor),
	/// An output spendable exclusively by our payment key (i.e., the private key that corresponds
	/// to the `payment_point` in [`ChannelSigner::pubkeys`]). The output type depends on the
	/// channel type negotiated.
	///
	/// On an anchor outputs channel, the witness in the spending input is:
	/// ```bitcoin
	/// <BIP 143 signature> <witness script>
	/// ```
	///
	/// Otherwise, it is:
	/// ```bitcoin
	/// <BIP 143 signature> <payment key>
	/// ```
	///
	/// These are generally the result of our counterparty having broadcast the current state,
	/// allowing us to claim the non-HTLC-encumbered outputs immediately, or after one confirmation
	/// in the case of anchor outputs channels.
	StaticPaymentOutput(StaticPaymentOutputDescriptor),
}

impl_writeable_tlv_based_enum_legacy!(SpendableOutputDescriptor,
	(0, StaticOutput) => {
		(0, outpoint, required),
		(1, channel_keys_id, option),
		(2, output, required),
	},
;
	(1, DelayedPaymentOutput),
	(2, StaticPaymentOutput),
);

impl SpendableOutputDescriptor {
	/// Turns this into a [`bitcoin::psbt::Input`] which can be used to create a
	/// [`Psbt`] which spends the given descriptor.
	///
	/// Note that this does not include any signatures, just the information required to
	/// construct the transaction and sign it.
	///
	/// This is not exported to bindings users as there is no standard serialization for an input.
	/// See [`Self::create_spendable_outputs_psbt`] instead.
	///
	/// The proprietary field is used to store add tweak for the signing key of this transaction.
	/// See the [`DelayedPaymentBasepoint::derive_add_tweak`] docs for more info on add tweak and how to use it.
	///
	/// To get the proprietary field use:
	/// ```
	/// use bitcoin::psbt::{Psbt};
	/// use bitcoin::hex::FromHex;
	///
	/// # let s = "70736274ff0100520200000001dee978529ab3e61a2987bea5183713d0e6d5ceb5ac81100fdb54a1a2\
	///	# 		 69cef505000000000090000000011f26000000000000160014abb3ab63280d4ccc5c11d6b50fd427a8\
	///	# 		 e19d6470000000000001012b10270000000000002200200afe4736760d814a2651bae63b572d935d9a\
	/// # 		 b74a1a16c01774e341a32afa763601054d63210394a27a700617f5b7aee72bd4f8076b5770a582b7fb\
	///	# 		 d1d4ee2ea3802cd3cfbe2067029000b27521034629b1c8fdebfaeb58a74cd181f485e2c462e594cb30\
	///	# 		 34dee655875f69f6c7c968ac20fc144c444b5f7370656e6461626c655f6f7574707574006164645f74\
	///	# 		 7765616b20a86534f38ad61dc580ef41c3886204adf0911b81619c1ad7a2f5b5de39a2ba600000";
	/// # let psbt = Psbt::deserialize(<Vec<u8> as FromHex>::from_hex(s).unwrap().as_slice()).unwrap();
	/// let key = bitcoin::psbt::raw::ProprietaryKey {
	/// 	prefix: "LDK_spendable_output".as_bytes().to_vec(),
	/// 	subtype: 0,
	/// 	key: "add_tweak".as_bytes().to_vec(),
	/// };
	/// let value = psbt
	/// 	.inputs
	/// 	.first()
	/// 	.expect("Unable to get add tweak as there are no inputs")
	/// 	.proprietary
	/// 	.get(&key)
	/// 	.map(|x| x.to_owned());
	/// ```
	pub fn to_psbt_input<T: secp256k1::Signing>(
		&self, secp_ctx: &Secp256k1<T>,
	) -> bitcoin::psbt::Input {
		match self {
			SpendableOutputDescriptor::StaticOutput { output, .. } => {
				// Is a standard P2WPKH, no need for witness script
				bitcoin::psbt::Input { witness_utxo: Some(output.clone()), ..Default::default() }
			},
			SpendableOutputDescriptor::DelayedPaymentOutput(DelayedPaymentOutputDescriptor {
				channel_transaction_parameters,
				per_commitment_point,
				revocation_pubkey,
				to_self_delay,
				output,
				..
			}) => {
				let delayed_payment_basepoint = channel_transaction_parameters
					.as_ref()
					.map(|params| params.holder_pubkeys.delayed_payment_basepoint);

				let (witness_script, add_tweak) =
					if let Some(basepoint) = delayed_payment_basepoint.as_ref() {
						// Required to derive signing key: privkey = basepoint_secret + SHA256(per_commitment_point || basepoint)
						let add_tweak = basepoint.derive_add_tweak(&per_commitment_point);
						let delayed_payment_key = DelayedPaymentKey(add_public_key_tweak(
							secp_ctx,
							&basepoint.to_public_key(),
							&add_tweak,
						));

						(
							Some(get_revokeable_redeemscript(
								&revocation_pubkey,
								*to_self_delay,
								&delayed_payment_key,
							)),
							Some(add_tweak),
						)
					} else {
						(None, None)
					};

				bitcoin::psbt::Input {
					witness_utxo: Some(output.clone()),
					witness_script,
					proprietary: add_tweak
						.map(|add_tweak| {
							[(
								bitcoin::psbt::raw::ProprietaryKey {
									// A non standard namespace for spendable outputs, used to store the tweak needed
									// to derive the private key
									prefix: "LDK_spendable_output".as_bytes().to_vec(),
									subtype: 0,
									key: "add_tweak".as_bytes().to_vec(),
								},
								add_tweak.as_byte_array().to_vec(),
							)]
							.into_iter()
							.collect()
						})
						.unwrap_or_default(),
					..Default::default()
				}
			},
			SpendableOutputDescriptor::StaticPaymentOutput(descriptor) => bitcoin::psbt::Input {
				witness_utxo: Some(descriptor.output.clone()),
				witness_script: descriptor.witness_script(),
				..Default::default()
			},
		}
	}

	/// Creates an unsigned [`Psbt`] which spends the given descriptors to
	/// the given outputs, plus an output to the given change destination (if sufficient
	/// change value remains). The PSBT will have a feerate, at least, of the given value.
	///
	/// The `locktime` argument is used to set the transaction's locktime. If `None`, the
	/// transaction will have a locktime of 0. It it recommended to set this to the current block
	/// height to avoid fee sniping, unless you have some specific reason to use a different
	/// locktime.
	///
	/// Returns the PSBT and expected max transaction weight.
	///
	/// Returns `Err(())` if the output value is greater than the input value minus required fee,
	/// if a descriptor was duplicated, or if an output descriptor `script_pubkey`
	/// does not match the one we can spend.
	///
	/// We do not enforce that outputs meet the dust limit or that any output scripts are standard.
	pub fn create_spendable_outputs_psbt<T: secp256k1::Signing + secp256k1::Verification>(
		secp_ctx: &Secp256k1<T>, descriptors: &[&SpendableOutputDescriptor], outputs: Vec<TxOut>,
		change_destination_script: ScriptBuf, feerate_sat_per_1000_weight: u32,
		locktime: Option<LockTime>,
	) -> Result<(Psbt, u64), ()> {
		let mut input = Vec::with_capacity(descriptors.len());
		let mut input_value = Amount::ZERO;
		let mut witness_weight = 0;
		let mut output_set = hash_set_with_capacity(descriptors.len());
		for outp in descriptors {
			match outp {
				SpendableOutputDescriptor::StaticPaymentOutput(descriptor) => {
					if !output_set.insert(descriptor.outpoint) {
						return Err(());
					}
					// The taproot `to_remote` 1-CSV tapleaf (and the anchor-channel P2WSH
					// `to_countersigner` script) both require sequence >= 1.
					let sequence = if descriptor.needs_csv_1_for_spend() || descriptor.is_taproot()
					{
						Sequence::from_consensus(1)
					} else {
						Sequence::ZERO
					};
					input.push(TxIn {
						previous_output: descriptor.outpoint.into_bitcoin_outpoint(),
						script_sig: ScriptBuf::new(),
						sequence,
						witness: Witness::new(),
					});
					// Taproot `to_remote` is a BIP341 script-path spend whose exact weight is
					// measured dynamically (secp is available here); legacy is the static bound.
					witness_weight +=
						descriptor.taproot_max_witness_weight(&secp_ctx).map_err(|_| ())?;
					#[cfg(feature = "grind_signatures")]
					{
						// Guarantees a low R signature. Only the legacy P2WSH/P2WPKH ECDSA
						// spend can be grinded; the taproot BIP340 Schnorr sig is fixed 64 bytes.
						if !descriptor.is_taproot() {
							witness_weight -= 1;
						}
					}
					input_value += descriptor.output.value;
				},
				SpendableOutputDescriptor::DelayedPaymentOutput(descriptor) => {
					if !output_set.insert(descriptor.outpoint) {
						return Err(());
					}
					input.push(TxIn {
						previous_output: descriptor.outpoint.into_bitcoin_outpoint(),
						script_sig: ScriptBuf::new(),
						sequence: Sequence(descriptor.to_self_delay as u32),
						witness: Witness::new(),
					});
					// Taproot `to_local` is a BIP341 script-path spend whose exact weight is
					// measured dynamically (secp is available here); legacy is the static bound.
					witness_weight +=
						descriptor.taproot_max_witness_weight(&secp_ctx).map_err(|_| ())?;
					#[cfg(feature = "grind_signatures")]
					{
						// Guarantees a low R signature. Only the legacy P2WSH ECDSA spend can
						// be grinded; the taproot BIP340 Schnorr sig is fixed 64 bytes.
						if !descriptor.is_taproot() {
							witness_weight -= 1;
						}
					}
					input_value += descriptor.output.value;
				},
				SpendableOutputDescriptor::StaticOutput { ref outpoint, ref output, .. } => {
					if !output_set.insert(*outpoint) {
						return Err(());
					}
					input.push(TxIn {
						previous_output: outpoint.into_bitcoin_outpoint(),
						script_sig: ScriptBuf::new(),
						sequence: Sequence::ZERO,
						witness: Witness::new(),
					});
					witness_weight += P2WPKH_WITNESS_WEIGHT;
					#[cfg(feature = "grind_signatures")]
					{
						// Guarantees a low R signature
						witness_weight -= 1;
					}
					input_value += output.value;
				},
			}
			if input_value > Amount::MAX_MONEY {
				return Err(());
			}
		}
		let mut tx = Transaction {
			version: Version::TWO,
			lock_time: locktime.unwrap_or(LockTime::ZERO),
			input,
			output: outputs,
		};
		let expected_max_weight = transaction_utils::maybe_add_change_output(
			&mut tx,
			input_value,
			witness_weight,
			feerate_sat_per_1000_weight,
			change_destination_script,
		)?;

		let psbt_inputs =
			descriptors.iter().map(|d| d.to_psbt_input(&secp_ctx)).collect::<Vec<_>>();
		let psbt = Psbt {
			inputs: psbt_inputs,
			outputs: vec![Default::default(); tx.output.len()],
			unsigned_tx: tx,
			xpub: Default::default(),
			version: 0,
			proprietary: Default::default(),
			unknown: Default::default(),
		};
		Ok((psbt, expected_max_weight))
	}

	/// Returns the outpoint of the spendable output.
	pub fn spendable_outpoint(&self) -> OutPoint {
		match self {
			Self::StaticOutput { outpoint, .. } => *outpoint,
			Self::StaticPaymentOutput(descriptor) => descriptor.outpoint,
			Self::DelayedPaymentOutput(descriptor) => descriptor.outpoint,
		}
	}
}

/// The parameters required to derive a channel signer via [`SignerProvider`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChannelDerivationParameters {
	/// The value in satoshis of the channel we're attempting to spend the anchor output of.
	pub value_satoshis: u64,
	/// The unique identifier to re-derive the signer for the associated channel.
	pub keys_id: [u8; 32],
	/// The necessary channel parameters that need to be provided to the signer.
	pub transaction_parameters: ChannelTransactionParameters,
}

impl_writeable_tlv_based!(ChannelDerivationParameters, {
	(0, value_satoshis, required),
	(2, keys_id, required),
	(4, transaction_parameters, (required: ReadableArgs, Some(value_satoshis.0.unwrap()))),
});

/// A descriptor used to sign for a commitment transaction's HTLC output.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HTLCDescriptor {
	/// The parameters required to derive the signer for the HTLC input.
	pub channel_derivation_parameters: ChannelDerivationParameters,
	/// The txid of the commitment transaction in which the HTLC output lives.
	pub commitment_txid: Txid,
	/// The number of the commitment transaction in which the HTLC output lives.
	pub per_commitment_number: u64,
	/// The key tweak corresponding to the number of the commitment transaction in which the HTLC
	/// output lives. This tweak is applied to all the basepoints for both parties in the channel to
	/// arrive at unique keys per commitment.
	///
	/// See <https://github.com/lightning/bolts/blob/master/03-transactions.md#keys> for more info.
	pub per_commitment_point: PublicKey,
	/// The feerate to use on the HTLC claiming transaction. This is always `0` for HTLCs
	/// originating from a channel supporting anchor outputs, otherwise it is the channel's
	/// negotiated feerate at the time the commitment transaction was built.
	pub feerate_per_kw: u32,
	/// The details of the HTLC as it appears in the commitment transaction.
	pub htlc: HTLCOutputInCommitment,
	/// The preimage, if `Some`, to claim the HTLC output with. If `None`, the timeout path must be
	/// taken.
	pub preimage: Option<PaymentPreimage>,
	/// The counterparty's signature required to spend the HTLC output.
	pub counterparty_sig: Signature,
	/// M9e-4: for `simple_taproot` channels the counterparty's per-HTLC signature is a
	/// BIP340 Schnorr sig over the 2-of-2 HTLC tapleaf (the ECDSA `counterparty_sig`
	/// above is an unused placeholder). The external-funding CPFP bump handler
	/// (`events::bump_transaction`) signs the holder-HTLC 2nd-level tx for anchor
	/// channels; for taproot it must build the script-path witness
	/// `[remote_schnorr, our_schnorr, (preimage), tapleaf, control_block]`, so the
	/// counterparty's Schnorr sig has to travel with the descriptor. `None` for legacy
	/// (P2WSH) channels.
	pub counterparty_sig_taproot: Option<schnorr::Signature>,
}

impl_writeable_tlv_based!(HTLCDescriptor, {
	(0, channel_derivation_parameters, required),
	(1, feerate_per_kw, (default_value, 0)),
	(2, commitment_txid, required),
	(4, per_commitment_number, required),
	(6, per_commitment_point, required),
	(8, htlc, required),
	(10, preimage, option),
	(12, counterparty_sig, required),
	(13, counterparty_sig_taproot, option),
});

impl HTLCDescriptor {
	/// Returns the outpoint of the HTLC output in the commitment transaction. This is the outpoint
	/// being spent by the HTLC input in the HTLC transaction.
	pub fn outpoint(&self) -> bitcoin::OutPoint {
		bitcoin::OutPoint {
			txid: self.commitment_txid,
			vout: self.htlc.transaction_output_index.unwrap(),
		}
	}

	/// Returns the UTXO to be spent by the HTLC input, which can be obtained via
	/// [`Self::unsigned_tx_input`].
	pub fn previous_utxo<C: secp256k1::Signing + secp256k1::Verification>(
		&self, secp: &Secp256k1<C>,
	) -> TxOut {
		let script_pubkey = if self
			.channel_derivation_parameters
			.transaction_parameters
			.channel_type_features
			.supports_simple_taproot()
		{
			// M9e-4: the HTLC output on a taproot commitment is a P2TR output (NUMS-tree
			// of offered/received tapleaves), not P2WSH.
			self.taproot_htlc_spk(secp)
		} else {
			self.witness_script(secp).to_p2wsh()
		};
		TxOut { script_pubkey, value: self.htlc.to_bitcoin_amount() }
	}

	/// M9e-4: the taproot HTLC output's scriptPubKey (`0x5120 || output_key`) for the
	/// simple-taproot HTLC tapscript tree, used as the prevout the 2nd-level
	/// HTLC-Success/Timeout tx spends.
	fn taproot_htlc_spk<C: secp256k1::Signing + secp256k1::Verification>(
		&self, secp: &Secp256k1<C>,
	) -> ScriptBuf {
		let channel_params =
			self.channel_derivation_parameters.transaction_parameters.as_holder_broadcastable();
		let keys = chan_utils::TxCreationKeys::from_channel_static_keys(
			&self.per_commitment_point,
			channel_params.broadcaster_pubkeys(),
			channel_params.countersignatory_pubkeys(),
			secp,
		);
		chan_utils::get_taproot_htlc_spk(
			secp,
			&self.htlc,
			&keys.broadcaster_htlc_key,
			&keys.countersignatory_htlc_key,
			&keys.revocation_key,
		)
	}

	/// Returns the unsigned transaction input spending the HTLC output in the commitment
	/// transaction.
	pub fn unsigned_tx_input(&self) -> TxIn {
		chan_utils::build_htlc_input(
			&self.commitment_txid,
			&self.htlc,
			&self.channel_derivation_parameters.transaction_parameters.channel_type_features,
		)
	}

	/// Returns the delayed output created as a result of spending the HTLC output in the commitment
	/// transaction.
	pub fn tx_output<C: secp256k1::Signing + secp256k1::Verification>(
		&self, secp: &Secp256k1<C>,
	) -> TxOut {
		let channel_params =
			self.channel_derivation_parameters.transaction_parameters.as_holder_broadcastable();
		let broadcaster_keys = channel_params.broadcaster_pubkeys();
		let counterparty_keys = channel_params.countersignatory_pubkeys();
		let broadcaster_delayed_key = DelayedPaymentKey::from_basepoint(
			secp,
			&broadcaster_keys.delayed_payment_basepoint,
			&self.per_commitment_point,
		);
		let counterparty_revocation_key = &RevocationKey::from_basepoint(
			&secp,
			&counterparty_keys.revocation_basepoint,
			&self.per_commitment_point,
		);
		chan_utils::build_htlc_output(
			self.feerate_per_kw,
			channel_params.contest_delay(),
			&self.htlc,
			channel_params.channel_type_features(),
			&broadcaster_delayed_key,
			&counterparty_revocation_key,
			secp,
		)
	}

	/// Returns the witness script of the HTLC output in the commitment transaction.
	pub fn witness_script<C: secp256k1::Signing + secp256k1::Verification>(
		&self, secp: &Secp256k1<C>,
	) -> ScriptBuf {
		let channel_params =
			self.channel_derivation_parameters.transaction_parameters.as_holder_broadcastable();
		let broadcaster_keys = channel_params.broadcaster_pubkeys();
		let counterparty_keys = channel_params.countersignatory_pubkeys();
		let broadcaster_htlc_key = HtlcKey::from_basepoint(
			secp,
			&broadcaster_keys.htlc_basepoint,
			&self.per_commitment_point,
		);
		let counterparty_htlc_key = HtlcKey::from_basepoint(
			secp,
			&counterparty_keys.htlc_basepoint,
			&self.per_commitment_point,
		);
		let counterparty_revocation_key = &RevocationKey::from_basepoint(
			&secp,
			&counterparty_keys.revocation_basepoint,
			&self.per_commitment_point,
		);
		chan_utils::get_htlc_redeemscript_with_explicit_keys(
			&self.htlc,
			channel_params.channel_type_features(),
			&broadcaster_htlc_key,
			&counterparty_htlc_key,
			&counterparty_revocation_key,
		)
	}

	/// Returns the fully signed witness required to spend the HTLC output in the commitment
	/// transaction.
	pub fn tx_input_witness(&self, signature: &Signature, witness_script: &Script) -> Witness {
		chan_utils::build_htlc_input_witness(
			signature,
			&self.counterparty_sig,
			&self.preimage,
			witness_script,
			&self.channel_derivation_parameters.transaction_parameters.channel_type_features,
		)
	}

	/// M9e-4: returns the fully signed BIP341 script-path witness for spending a
	/// **taproot** HTLC output (the 2nd-level HTLC-Success/Timeout tx). Mirrors the
	/// malleable-path witness built at `chain::package::get_maybe_signed_htlc_tx`:
	/// `[remote_schnorr, our_schnorr, (preimage), htlc_tapleaf, control_block]` over
	/// the 2-of-2 HTLC tapleaf. `our_sig` is produced by
	/// `sign_holder_htlc_transaction_taproot`; the counterparty's pre-signed Schnorr
	/// sig is carried in `self.counterparty_sig_taproot`. Used by the external-funding
	/// CPFP bump handler for anchor (zero-fee) taproot channels.
	pub fn taproot_tx_input_witness<C: secp256k1::Signing + secp256k1::Verification>(
		&self, our_sig: &schnorr::Signature, secp: &Secp256k1<C>,
	) -> Result<Witness, ()> {
		let remote_sig = self.counterparty_sig_taproot.as_ref().ok_or(())?;
		let channel_params =
			self.channel_derivation_parameters.transaction_parameters.as_holder_broadcastable();
		let keys = chan_utils::TxCreationKeys::from_channel_static_keys(
			&self.per_commitment_point,
			channel_params.broadcaster_pubkeys(),
			channel_params.countersignatory_pubkeys(),
			secp,
		);
		let leaf = chan_utils::taproot_htlc_remote_sig_leaf(
			&self.htlc,
			&keys.broadcaster_htlc_key,
			&keys.countersignatory_htlc_key,
		);
		let spend_info = chan_utils::taproot_htlc_spend_info(
			secp,
			&self.htlc,
			&keys.broadcaster_htlc_key,
			&keys.countersignatory_htlc_key,
			&keys.revocation_key,
		);
		chan_utils::build_taproot_htlc_input_witness(
			our_sig,
			remote_sig,
			&self.preimage,
			&leaf,
			&spend_info,
		)
		.map_err(|_| ())
	}

	/// M9e-4: the worst-case serialized weight (witness units) of the BIP341 script-path
	/// witness this descriptor's taproot HTLC input is spent with — computed
	/// **dynamically** by BUILDING the real witness (the actual tapleaf script + control
	/// block from this HTLC's spend info, with max-size dummy Schnorr sigs) and measuring
	/// it, rather than a hardcoded constant. This adapts automatically to the tapleaf
	/// script length, control-block depth, and sig encoding, so it stays exact if the
	/// taproot HTLC script ever changes. Used by the external-funding CPFP bump handler to
	/// size each taproot HTLC input's `satisfaction_weight`.
	///
	/// The signer's real Schnorr sigs are 64-byte BIP340 sigs; `build_taproot_htlc_input_witness`
	/// appends the sighash-type byte, so the on-chain witness element is 65 bytes — exactly
	/// what a 64-byte dummy sig measures here. This is the worst case (sigs are fixed-length),
	/// so the result is a tight, never-underestimating upper bound.
	pub fn taproot_max_witness_weight<C: secp256k1::Signing + secp256k1::Verification>(
		&self, secp: &Secp256k1<C>,
	) -> Result<u64, ()> {
		// A 64-byte all-zero BIP340 Schnorr signature is a valid-length placeholder; only its
		// serialized length matters for the weight measurement (not its validity).
		let dummy_sig = schnorr::Signature::from_slice(&[0u8; 64]).map_err(|_| ())?;
		let channel_params =
			self.channel_derivation_parameters.transaction_parameters.as_holder_broadcastable();
		let keys = chan_utils::TxCreationKeys::from_channel_static_keys(
			&self.per_commitment_point,
			channel_params.broadcaster_pubkeys(),
			channel_params.countersignatory_pubkeys(),
			secp,
		);
		let leaf = chan_utils::taproot_htlc_remote_sig_leaf(
			&self.htlc,
			&keys.broadcaster_htlc_key,
			&keys.countersignatory_htlc_key,
		);
		let spend_info = chan_utils::taproot_htlc_spend_info(
			secp,
			&self.htlc,
			&keys.broadcaster_htlc_key,
			&keys.countersignatory_htlc_key,
			&keys.revocation_key,
		);
		let witness = chan_utils::build_taproot_htlc_input_witness(
			&dummy_sig,
			&dummy_sig,
			&self.preimage,
			&leaf,
			&spend_info,
		)
		.map_err(|_| ())?;
		// `witness.size()` is the exact serialized witness for this input. The per-input
		// satisfaction-weight model omits the per-tx BIP141 segwit marker+flag (2 WU),
		// which the conservative P2WSH constants happen to absorb but this exact taproot
		// measurement does not; attribute it here so the bump estimate stays a safe upper
		// bound (well within the 2% tightness check, even with multiple HTLC inputs).
		Ok(witness.size() as u64 + chan_utils::SEGWIT_MARKER_FLAG_WEIGHT)
	}
}

/// A trait to handle Lightning channel key material without concretizing the channel type or
/// the signature mechanism.
///
/// Several methods allow errors to be returned to support async signing. In such cases, the
/// signing operation can be replayed by calling [`ChannelManager::signer_unblocked`] once the
/// result is ready, at which point the channel operation will resume. Methods which allow for
/// async results are explicitly documented as such
///
/// [`ChannelManager::signer_unblocked`]: crate::ln::channelmanager::ChannelManager::signer_unblocked
pub trait ChannelSigner {
	/// Gets the per-commitment point for a specific commitment number
	///
	/// Note that the commitment number starts at `(1 << 48) - 1` and counts backwards.
	///
	/// This method is *not* asynchronous. This method is expected to always return `Ok`
	/// immediately after we reconnect to peers, and returning an `Err` may lead to an immediate
	/// `panic`. This method will be made asynchronous in a future release.
	fn get_per_commitment_point(
		&self, idx: u64, secp_ctx: &Secp256k1<secp256k1::All>,
	) -> Result<PublicKey, ()>;

	/// Gets the commitment secret for a specific commitment number as part of the revocation process
	///
	/// An external signer implementation should error here if the commitment was already signed
	/// and should refuse to sign it in the future.
	///
	/// May be called more than once for the same index.
	///
	/// Note that the commitment number starts at `(1 << 48) - 1` and counts backwards.
	///
	/// An `Err` can be returned to signal that the signer is unavailable/cannot produce a valid
	/// signature and should be retried later. Once the signer is ready to provide a signature after
	/// previously returning an `Err`, [`ChannelManager::signer_unblocked`] must be called.
	///
	/// [`ChannelManager::signer_unblocked`]: crate::ln::channelmanager::ChannelManager::signer_unblocked
	fn release_commitment_secret(&self, idx: u64) -> Result<[u8; 32], ()>;

	/// Validate the counterparty's signatures on the holder commitment transaction and HTLCs.
	///
	/// This is required in order for the signer to make sure that releasing a commitment
	/// secret won't leave us without a broadcastable holder transaction.
	/// Policy checks should be implemented in this function, including checking the amount
	/// sent to us and checking the HTLCs.
	///
	/// The preimages of outbound HTLCs that were fulfilled since the last commitment are provided.
	/// A validating signer should ensure that an HTLC output is removed only when the matching
	/// preimage is provided, or when the value to holder is restored.
	///
	/// Note that all the relevant preimages will be provided, but there may also be additional
	/// irrelevant or duplicate preimages.
	///
	/// This method is *not* asynchronous. If an `Err` is returned, the channel will be immediately
	/// closed. If you wish to make this operation asynchronous, you should instead return `Ok(())`
	/// and pause future signing operations until this validation completes.
	fn validate_holder_commitment(
		&self, holder_tx: &HolderCommitmentTransaction,
		outbound_htlc_preimages: Vec<PaymentPreimage>,
	) -> Result<(), ()>;

	/// Validate the counterparty's revocation.
	///
	/// This is required in order for the signer to make sure that the state has moved
	/// forward and it is safe to sign the next counterparty commitment.
	///
	/// This method is *not* asynchronous. If an `Err` is returned, the channel will be immediately
	/// closed. If you wish to make this operation asynchronous, you should instead return `Ok(())`
	/// and pause future signing operations until this validation completes.
	fn validate_counterparty_revocation(&self, idx: u64, secret: &SecretKey) -> Result<(), ()>;

	/// Returns the holder channel public keys and basepoints. This should only be called once
	/// during channel creation and as such implementations are allowed undefined behavior if
	/// called more than once.
	///
	/// This method is *not* asynchronous. Instead, the value must be computed locally or in
	/// advance and cached.
	fn pubkeys(&self, secp_ctx: &Secp256k1<secp256k1::All>) -> ChannelPublicKeys;

	/// Returns a new funding pubkey (i.e. our public which is used in a 2-of-2 with the
	/// counterparty's key to to lock the funds on-chain) for a spliced channel.
	///
	/// `splice_parent_funding_txid` can be used to compute a tweak with which to rotate the base
	/// key (which will then be available later in signing operations via
	/// [`ChannelTransactionParameters::splice_parent_funding_txid`]).
	///
	/// This method is *not* asynchronous. Instead, the value must be cached locally.
	fn new_funding_pubkey(
		&self, splice_parent_funding_txid: Txid, secp_ctx: &Secp256k1<secp256k1::All>,
	) -> PublicKey;

	/// Returns an arbitrary identifier describing the set of keys which are provided back to you in
	/// some [`SpendableOutputDescriptor`] types. This should be sufficient to identify this
	/// [`EcdsaChannelSigner`] object uniquely and lookup or re-derive its keys.
	///
	/// This method is *not* asynchronous. Instead, the value must be cached locally.
	fn channel_keys_id(&self) -> [u8; 32];
}

/// Represents the secret key material used for encrypting Peer Storage.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct PeerStorageKey {
	/// Represents the key used to encrypt and decrypt Peer Storage.
	pub inner: [u8; 32],
}

/// A secret key used to authenticate message contexts in received [`BlindedMessagePath`]s.
///
/// This key ensures that a node only accepts incoming messages delivered through
/// blinded paths that it constructed itself.
///
/// [`BlindedMessagePath`]: crate::blinded_path::message::BlindedMessagePath
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ReceiveAuthKey(pub [u8; 32]);

/// Specifies the recipient of an invoice.
///
/// This indicates to [`NodeSigner::sign_invoice`] what node secret key should be used to sign
/// the invoice.
#[derive(Clone, Copy)]
pub enum Recipient {
	/// The invoice should be signed with the local node secret key.
	Node,
	/// The invoice should be signed with the phantom node secret key. This secret key must be the
	/// same for all nodes participating in the [phantom node payment].
	///
	/// [phantom node payment]: PhantomKeysManager
	PhantomNode,
}

/// A trait that describes a source of entropy.
pub trait EntropySource {
	/// Gets a unique, cryptographically-secure, random 32-byte value. This method must return a
	/// different value each time it is called.
	fn get_secure_random_bytes(&self) -> [u8; 32];
}

/// A trait that can handle cryptographic operations at the scope level of a node.
pub trait NodeSigner {
	/// Get the [`ExpandedKey`] which provides cryptographic material for various Lightning Network operations.
	///
	/// This key set is used for:
	/// - Encrypting and decrypting inbound payment metadata
	/// - Authenticating payment hashes (both LDK-provided and user-provided)
	/// - Supporting BOLT 12 Offers functionality (key derivation and authentication)
	/// - Authenticating spontaneous payments' metadata
	///
	/// This method must return the same value each time it is called.
	///
	/// If the implementor of this trait supports [phantom node payments], then every node that is
	/// intended to be included in the phantom invoice route hints must return the same value from
	/// this method. This is because LDK avoids storing inbound payment data. Instead, this key
	/// is used to construct a payment secret which is received in the payment onion and used to
	/// reconstruct the payment preimage. Therefore, for a payment to be receivable by multiple
	/// nodes, they must share the same key.
	///
	/// [phantom node payments]: PhantomKeysManager
	fn get_expanded_key(&self) -> ExpandedKey;

	/// Defines a method to derive a 32-byte encryption key for peer storage.
	///
	/// Implementations of this method must derive a secure encryption key.
	/// The key is used to encrypt or decrypt backups of our state stored with our peers.
	///
	/// Thus, if you wish to rely on recovery using this method, you should use a key which
	/// can be re-derived from data which would be available after state loss (eg the wallet seed).
	fn get_peer_storage_key(&self) -> PeerStorageKey;

	/// Returns the [`ReceiveAuthKey`] used to authenticate incoming [`BlindedMessagePath`] contexts.
	///
	/// This key is used as additional associated data (AAD) during MAC verification of the
	/// [`MessageContext`] at the final hop of a blinded path. It ensures that only paths
	/// constructed by this node will be accepted, preventing unauthorized parties from forging
	/// valid-looking messages.
	///
	/// Implementers must ensure that this key remains secret and consistent across invocations.
	///
	/// [`BlindedMessagePath`]: crate::blinded_path::message::BlindedMessagePath
	/// [`MessageContext`]: crate::blinded_path::message::MessageContext
	fn get_receive_auth_key(&self) -> ReceiveAuthKey;

	/// Get node id based on the provided [`Recipient`].
	///
	/// This method must return the same value each time it is called with a given [`Recipient`]
	/// parameter.
	///
	/// Errors if the [`Recipient`] variant is not supported by the implementation.
	fn get_node_id(&self, recipient: Recipient) -> Result<PublicKey, ()>;

	/// Gets the ECDH shared secret of our node secret and `other_key`, multiplying by `tweak` if
	/// one is provided. Note that this tweak can be applied to `other_key` instead of our node
	/// secret, though this is less efficient.
	///
	/// Note that if this fails while attempting to forward an HTLC, LDK will panic. The error
	/// should be resolved to allow LDK to resume forwarding HTLCs.
	///
	/// Errors if the [`Recipient`] variant is not supported by the implementation.
	fn ecdh(
		&self, recipient: Recipient, other_key: &PublicKey, tweak: Option<&Scalar>,
	) -> Result<SharedSecret, ()>;

	/// Sign an invoice.
	///
	/// By parameterizing by the raw invoice bytes instead of the hash, we allow implementors of
	/// this trait to parse the invoice and make sure they're signing what they expect, rather than
	/// blindly signing the hash.
	///
	/// The `hrp_bytes` are ASCII bytes, while the `invoice_data` is base32.
	///
	/// The secret key used to sign the invoice is dependent on the [`Recipient`].
	///
	/// Errors if the [`Recipient`] variant is not supported by the implementation.
	fn sign_invoice(
		&self, invoice: &RawBolt11Invoice, recipient: Recipient,
	) -> Result<RecoverableSignature, ()>;

	/// Signs the [`TaggedHash`] of a BOLT 12 invoice.
	///
	/// May be called by a function passed to [`UnsignedBolt12Invoice::sign`] where `invoice` is the
	/// callee.
	///
	/// Implementors may check that the `invoice` is expected rather than blindly signing the tagged
	/// hash. An `Ok` result should sign `invoice.tagged_hash().as_digest()` with the node's signing
	/// key or an ephemeral key to preserve privacy, whichever is associated with
	/// [`UnsignedBolt12Invoice::signing_pubkey`].
	///
	/// [`TaggedHash`]: crate::offers::merkle::TaggedHash
	fn sign_bolt12_invoice(
		&self, invoice: &UnsignedBolt12Invoice,
	) -> Result<schnorr::Signature, ()>;

	/// Sign a gossip message.
	///
	/// Note that if this fails, LDK may panic and the message will not be broadcast to the network
	/// or a possible channel counterparty. If LDK panics, the error should be resolved to allow the
	/// message to be broadcast, as otherwise it may prevent one from receiving funds over the
	/// corresponding channel.
	fn sign_gossip_message(&self, msg: UnsignedGossipMessage) -> Result<Signature, ()>;

	/// Sign an arbitrary message with the node's secret key.
	///
	/// Creates a digital signature of a message given the node's secret. The message is prefixed
	/// with "Lightning Signed Message:" before signing. See [this description of the format](https://web.archive.org/web/20191010011846/https://twitter.com/rusty_twit/status/1182102005914800128)
	/// for more details.
	///
	/// A receiver knowing the node's id and the message can be sure that the signature was generated by the caller.
	/// An `Err` can be returned to signal that the signer is unavailable / cannot produce a valid
	/// signature.
	fn sign_message(&self, msg: &[u8]) -> Result<String, ()>;
}

/// A trait that describes a wallet capable of creating a spending [`Transaction`] from a set of
/// [`SpendableOutputDescriptor`]s.
pub trait OutputSpender {
	/// Creates a [`Transaction`] which spends the given descriptors to the given outputs, plus an
	/// output to the given change destination (if sufficient change value remains). The
	/// transaction will have a feerate, at least, of the given value.
	///
	/// The `locktime` argument is used to set the transaction's locktime. If `None`, the
	/// transaction will have a locktime of 0. It it recommended to set this to the current block
	/// height to avoid fee sniping, unless you have some specific reason to use a different
	/// locktime.
	///
	/// Returns `Err(())` if the output value is greater than the input value minus required fee,
	/// if a descriptor was duplicated, or if an output descriptor `script_pubkey`
	/// does not match the one we can spend.
	fn spend_spendable_outputs(
		&self, descriptors: &[&SpendableOutputDescriptor], outputs: Vec<TxOut>,
		change_destination_script: ScriptBuf, feerate_sat_per_1000_weight: u32,
		locktime: Option<LockTime>, secp_ctx: &Secp256k1<All>,
	) -> Result<Transaction, ()>;
}

// Primarily needed in doctests because of https://github.com/rust-lang/rust/issues/67295
/// A dynamic [`SignerProvider`] temporarily needed for doc tests.
///
/// This is not exported to bindings users as it is not intended for public consumption.
#[doc(hidden)]
pub type DynSignerProvider =
	dyn SignerProvider<EcdsaSigner = InMemorySigner, TaprootSigner = InMemorySigner>;

/// A trait that can return signer instances for individual channels.
pub trait SignerProvider {
	/// A type which implements [`EcdsaChannelSigner`] which will be returned by [`Self::derive_channel_signer`].
	type EcdsaSigner: EcdsaChannelSigner;
	/// A type which implements [`TaprootChannelSigner`]
	type TaprootSigner: TaprootChannelSigner;

	/// Generates a unique `channel_keys_id` that can be used to obtain a [`Self::EcdsaSigner`] through
	/// [`SignerProvider::derive_channel_signer`]. The `user_channel_id` is provided to allow
	/// implementations of [`SignerProvider`] to maintain a mapping between itself and the generated
	/// `channel_keys_id`.
	///
	/// This method must return a different value each time it is called.
	fn generate_channel_keys_id(&self, inbound: bool, user_channel_id: u128) -> [u8; 32];

	/// Derives the private key material backing a `Signer`.
	///
	/// To derive a new `Signer`, a fresh `channel_keys_id` should be obtained through
	/// [`SignerProvider::generate_channel_keys_id`]. Otherwise, an existing `Signer` can be
	/// re-derived from its `channel_keys_id`, which can be obtained through its trait method
	/// [`ChannelSigner::channel_keys_id`].
	fn derive_channel_signer(&self, channel_keys_id: [u8; 32]) -> Self::EcdsaSigner;

	/// Derives the [`Self::TaprootSigner`] for a **simple taproot channel**
	/// (`docs/TAPROOT-CHANNELS-BUILD-SPEC.md`). This is the taproot analogue of
	/// [`Self::derive_channel_signer`]: it is called instead of that method when
	/// the negotiated `channel_type` has `option_simple_taproot`, so the channel
	/// can hold a `ChannelSignerType::Taproot(_)` and drive the MuSig2 key-path
	/// nonce-exchange flow. It re-derives from the same `channel_keys_id` key
	/// material — for providers where `TaprootSigner == EcdsaSigner` (e.g.
	/// [`KeysManager`], the test harness) it is the same signer.
	fn derive_taproot_channel_signer(&self, channel_keys_id: [u8; 32]) -> Self::TaprootSigner;

	/// Get a script pubkey which we send funds to when claiming on-chain contestable outputs.
	///
	/// If this function returns an error, this will result in a channel failing to open.
	///
	/// This method should return a different value each time it is called, to avoid linking
	/// on-chain funds across channels as controlled to the same user. `channel_keys_id` may be
	/// used to derive a unique value for each channel.
	fn get_destination_script(&self, channel_keys_id: [u8; 32]) -> Result<ScriptBuf, ()>;

	/// Get a script pubkey which we will send funds to when closing a channel.
	///
	/// If this function returns an error, this will result in a channel failing to open or close.
	/// In the event of a failure when the counterparty is initiating a close, this can result in a
	/// channel force close.
	///
	/// This method should return a different value each time it is called, to avoid linking
	/// on-chain funds across channels as controlled to the same user.
	fn get_shutdown_scriptpubkey(&self) -> Result<ShutdownScript, ()>;
}

/// A helper trait that describes an on-chain wallet capable of returning a (change) destination
/// script.
///
/// This is not exported to bindings users as async is only supported in Rust.
pub trait ChangeDestinationSource {
	/// Returns a script pubkey which can be used as a change destination for
	/// [`OutputSpender::spend_spendable_outputs`].
	///
	/// This method should return a different value each time it is called, to avoid linking
	/// on-chain funds controlled to the same user.
	fn get_change_destination_script<'a>(&'a self) -> AsyncResult<'a, ScriptBuf, ()>;
}

/// A synchronous helper trait that describes an on-chain wallet capable of returning a (change) destination script.
pub trait ChangeDestinationSourceSync {
	/// Returns a script pubkey which can be used as a change destination for
	/// [`OutputSpender::spend_spendable_outputs`].
	///
	/// This method should return a different value each time it is called, to avoid linking
	/// on-chain funds controlled to the same user.
	fn get_change_destination_script(&self) -> Result<ScriptBuf, ()>;
}

/// A wrapper around [`ChangeDestinationSource`] to allow for async calls.
///
/// You should likely never use this directly but rather allow LDK to build this when required to
/// build higher-level sync wrappers.
#[doc(hidden)]
pub struct ChangeDestinationSourceSyncWrapper<T: Deref>(T)
where
	T::Target: ChangeDestinationSourceSync;

impl<T: Deref> ChangeDestinationSourceSyncWrapper<T>
where
	T::Target: ChangeDestinationSourceSync,
{
	/// Creates a new [`ChangeDestinationSourceSyncWrapper`].
	pub fn new(source: T) -> Self {
		Self(source)
	}
}
impl<T: Deref> ChangeDestinationSource for ChangeDestinationSourceSyncWrapper<T>
where
	T::Target: ChangeDestinationSourceSync,
{
	fn get_change_destination_script<'a>(&'a self) -> AsyncResult<'a, ScriptBuf, ()> {
		let script = self.0.get_change_destination_script();
		Box::pin(async move { script })
	}
}

impl<T: Deref> Deref for ChangeDestinationSourceSyncWrapper<T>
where
	T::Target: ChangeDestinationSourceSync,
{
	type Target = Self;
	fn deref(&self) -> &Self {
		self
	}
}

mod sealed {
	use bitcoin::secp256k1::{Scalar, SecretKey};

	#[derive(Clone, PartialEq)]
	pub struct MaybeTweakedSecretKey(pub(super) SecretKey);

	impl From<SecretKey> for MaybeTweakedSecretKey {
		fn from(value: SecretKey) -> Self {
			Self(value)
		}
	}

	impl MaybeTweakedSecretKey {
		pub fn with_tweak(&self, tweak: Option<Scalar>) -> SecretKey {
			tweak
				.map(|tweak| {
					self.0
						.add_tweak(&tweak)
						.expect("Addition only fails if the tweak is the inverse of the key")
				})
				.unwrap_or(self.0)
		}
	}
}

/// Computes the tweak to apply to the base funding key of a channel.
///
/// The tweak is computed similar to existing tweaks used in
/// [BOLT-3](https://github.com/lightning/bolts/blob/master/03-transactions.md#key-derivation):
///
/// 1. We use the txid of the funding transaction the splice transaction is spending instead of the
///    `per_commitment_point` to guarantee uniqueness.
/// 2. We include the private key instead of the public key to guarantee only those with knowledge
///    of it can re-derive the new funding key.
///
///   tweak = SHA256(splice_parent_funding_txid || base_funding_secret_key)
///   tweaked_funding_key = base_funding_key + tweak
///
/// While the use of this tweak is not required (signers may choose to compute a tweak of their
/// choice), signers must ensure their tweak guarantees the two properties mentioned above:
/// uniqueness and derivable only by one or both of the channel participants.
pub fn compute_funding_key_tweak(
	base_funding_secret_key: &SecretKey, splice_parent_funding_txid: &Txid,
) -> Scalar {
	let mut sha = Sha256::engine();
	sha.input(splice_parent_funding_txid.as_byte_array());
	sha.input(&base_funding_secret_key.secret_bytes());
	Scalar::from_be_bytes(Sha256::from_engine(sha).to_byte_array()).unwrap()
}

/// A simple implementation of [`EcdsaChannelSigner`] that just keeps the private keys in memory.
///
/// This implementation performs no policy checks and is insufficient by itself as
/// a secure external signer.
pub struct InMemorySigner {
	/// Holder secret key in the 2-of-2 multisig script of a channel. This key also backs the
	/// holder's anchor output in a commitment transaction, if one is present.
	funding_key: sealed::MaybeTweakedSecretKey,
	/// Holder secret key for blinded revocation pubkey.
	pub revocation_base_key: SecretKey,
	/// Holder secret key used for our balance in counterparty-broadcasted commitment transactions,
	/// old-style derivation.
	payment_key_v1: SecretKey,
	/// Holder secret key used for our balance in counterparty-broadcasted commitment transactions,
	/// new-style derivation.
	payment_key_v2: SecretKey,
	/// Which of [`Self::payment_key_v1`] and [`Self::payment_key_v2`] to use by default.
	v2_remote_key_derivation: bool,
	/// Holder secret key used in an HTLC transaction.
	pub delayed_payment_base_key: SecretKey,
	/// Holder HTLC secret key used in commitment transaction HTLC outputs.
	pub htlc_base_key: SecretKey,
	/// Commitment seed.
	pub commitment_seed: [u8; 32],
	/// Key derivation parameters.
	channel_keys_id: [u8; 32],
	/// A source of random bytes.
	entropy_source: RandomBytes,
	/// Late-bound per-channel MuSig2 (simple-taproot) signing context.
	///
	/// The `TaprootChannelSigner` trait surface of this fork passes neither the
	/// counterparty funding pubkey nor the funding prevout into the MuSig2
	/// methods, so a funding key-path partial cannot be produced from the trait
	/// arguments alone: it needs the counterparty funding pubkey (to build the
	/// per-channel `KeyAggContext` → the `0x5120||Q` funding scriptPubKey) and the
	/// funding amount (committed in the BIP341 key-path sighash). The
	/// nonce-exchange handler supplies it via [`InMemorySigner::provide_taproot_context`].
	///
	/// This is **ephemeral**, never persisted (this fork does not serialize the
	/// signer; the monitor re-derives it via `derive_channel_signer` and the
	/// handler re-supplies the context from the reloaded `FundingScope`), and is
	/// excluded from `PartialEq`/`Clone`-of-state — a clone starts with no context.
	taproot_ctx: Arc<Mutex<Option<TaprootSignerContext>>>,
}

/// The late-bound per-channel data the MuSig2 (`TaprootChannelSigner`) bodies of
/// [`InMemorySigner`] need but the trait surface does not hand them. Supplied by
/// the `channel.rs` nonce-exchange handler via
/// [`InMemorySigner::provide_taproot_context`]. Mirrors
/// `quid_ln::validating_signer::TaprootSignerContext`.
#[derive(Clone)]
pub struct TaprootSignerContext {
	/// The counterparty's 33-byte compressed funding pubkey.
	pub counterparty_funding_pubkey: PublicKey,
	/// The channel funding amount in satoshis (committed in the key-path sighash).
	pub funding_value_sat: u64,
	/// The counterparty's current cooperative-close nonce (their `shutdown_nonce`,
	/// or the nonce from their previous `closing_sig` on an RBF round). Required by
	/// [`TaprootChannelSigner::partially_sign_closing_transaction`], which the
	/// trait surface passes no nonce to. `None` until `shutdown` is exchanged.
	pub counterparty_closing_nonce: Option<PublicNonce>,
	/// The **cooperative-close round index** (`0` for the `shutdown`/first
	/// `closing_signed`, incremented for every subsequent fee-negotiation /RBF
	/// round). The closing MuSig2 secret nonce is derived at the per-round height
	/// [`closing_nonce_height`]`(closing_round)` so no two distinct close
	/// transactions (different fees ⇒ different sighash messages) are ever signed
	/// with the same nonce — which would otherwise leak the funding private key
	/// (`docs/TAPROOT-CHANNELS-BUILD-SPEC.md` §9f-0). The handler bumps this each
	/// round before supplying the context; signing and the advertised
	/// `shutdown_nonce`/`next_closee_nonce` MUST use the same round so the
	/// advertised nonce equals the nonce the partial is computed with.
	pub closing_round: u64,
	/// For a **spliced** funding scope: the `prev_funding_txid` the new funding key
	/// was rotated from (BOLT #995 / spec §9c). When set, the signer derives BOTH its
	/// individual funding key AND the KeyAggContext from the ROTATED key
	/// (`funding_key(Some(txid))`), so the aggregate matches the new `0x5120||Q'` the
	/// splice funding output commits to. `None` for the original (un-spliced) funding,
	/// where the base funding key is used. (The shared-input splice SPEND uses the OLD
	/// `Q` and is handled separately via `partially_sign_splice_shared_input`, which
	/// always uses the base key; this field is for the NEW commitment scope.)
	pub splice_parent_funding_txid: Option<bitcoin::Txid>,
}

impl PartialEq for InMemorySigner {
	fn eq(&self, other: &Self) -> bool {
		self.funding_key == other.funding_key
			&& self.revocation_base_key == other.revocation_base_key
			&& self.payment_key_v1 == other.payment_key_v1
			&& self.payment_key_v2 == other.payment_key_v2
			&& self.v2_remote_key_derivation == other.v2_remote_key_derivation
			&& self.delayed_payment_base_key == other.delayed_payment_base_key
			&& self.htlc_base_key == other.htlc_base_key
			&& self.commitment_seed == other.commitment_seed
			&& self.channel_keys_id == other.channel_keys_id
	}
}

impl Clone for InMemorySigner {
	fn clone(&self) -> Self {
		Self {
			funding_key: self.funding_key.clone(),
			revocation_base_key: self.revocation_base_key.clone(),
			payment_key_v1: self.payment_key_v1.clone(),
			payment_key_v2: self.payment_key_v2.clone(),
			v2_remote_key_derivation: self.v2_remote_key_derivation,
			delayed_payment_base_key: self.delayed_payment_base_key.clone(),
			htlc_base_key: self.htlc_base_key.clone(),
			commitment_seed: self.commitment_seed.clone(),
			channel_keys_id: self.channel_keys_id,
			entropy_source: RandomBytes::new(self.get_secure_random_bytes()),
			// Share the late-bound taproot context across clones: LDK clones the
			// signer freely (e.g. into the monitor), and the nonce-exchange handler
			// may have already supplied the context to one clone. An `Arc<Mutex<_>>`
			// keeps every clone pointed at the same (ephemeral) context cell.
			taproot_ctx: Arc::clone(&self.taproot_ctx),
		}
	}
}

impl InMemorySigner {
	#[cfg(any(feature = "_test_utils", test))]
	pub fn new(
		funding_key: SecretKey, revocation_base_key: SecretKey, payment_key_v1: SecretKey,
		payment_key_v2: SecretKey, v2_remote_key_derivation: bool,
		delayed_payment_base_key: SecretKey, htlc_base_key: SecretKey, commitment_seed: [u8; 32],
		channel_keys_id: [u8; 32], rand_bytes_unique_start: [u8; 32],
	) -> InMemorySigner {
		InMemorySigner {
			funding_key: sealed::MaybeTweakedSecretKey::from(funding_key),
			revocation_base_key,
			payment_key_v1,
			payment_key_v2,
			v2_remote_key_derivation,
			delayed_payment_base_key,
			htlc_base_key,
			commitment_seed,
			channel_keys_id,
			entropy_source: RandomBytes::new(rand_bytes_unique_start),
			taproot_ctx: Arc::new(Mutex::new(None)),
		}
	}

	#[cfg(not(any(feature = "_test_utils", test)))]
	fn new(
		funding_key: SecretKey, revocation_base_key: SecretKey, payment_key_v1: SecretKey,
		payment_key_v2: SecretKey, v2_remote_key_derivation: bool,
		delayed_payment_base_key: SecretKey, htlc_base_key: SecretKey, commitment_seed: [u8; 32],
		channel_keys_id: [u8; 32], rand_bytes_unique_start: [u8; 32],
	) -> InMemorySigner {
		InMemorySigner {
			funding_key: sealed::MaybeTweakedSecretKey::from(funding_key),
			revocation_base_key,
			payment_key_v1,
			payment_key_v2,
			v2_remote_key_derivation,
			delayed_payment_base_key,
			htlc_base_key,
			commitment_seed,
			channel_keys_id,
			entropy_source: RandomBytes::new(rand_bytes_unique_start),
			taproot_ctx: Arc::new(Mutex::new(None)),
		}
	}

	/// Holder secret key in the 2-of-2 multisig script of a channel. This key also backs the
	/// holder's anchor output in a commitment transaction, if one is present.
	pub fn funding_key(&self, splice_parent_funding_txid: Option<Txid>) -> SecretKey {
		let tweak = splice_parent_funding_txid
			.map(|txid| compute_funding_key_tweak(&self.funding_key.with_tweak(None), &txid));
		self.funding_key.with_tweak(tweak)
	}

	/// Supply the late-bound per-channel taproot (MuSig2) signing context.
	///
	/// Called by the `channel.rs` nonce-exchange handler as soon as the
	/// counterparty funding pubkey + funding amount are known (the channel's
	/// `channel_transaction_parameters` carry the counterparty parameters and
	/// funding outpoint). Idempotent for the same context; re-supplying a
	/// different one replaces it (a splice rebinds `Q`, and each close round
	/// re-supplies the peer's current closing nonce). This is the data the MuSig2
	/// funding key-path bodies need but the `TaprootChannelSigner` trait surface
	/// does not pass. See [`TaprootSignerContext`].
	pub fn provide_taproot_context(&self, ctx: TaprootSignerContext) {
		if let Ok(mut slot) = self.taproot_ctx.lock() {
			*slot = Some(ctx);
		}
	}

	/// Build the cached per-channel KeySorted + taproot-tweaked `KeyAggContext`,
	/// our signer index, the counterparty index, the funding amount, and the
	/// `0x5120||Q` funding scriptPubKey that the BIP341 key-path sighash commits
	/// to, from the handler-supplied [`TaprootSignerContext`]. `Err(())` if no
	/// context has been supplied yet.
	/// The (rotated, for a splice) holder funding SECRET key the current taproot
	/// context's funding scope signs with — `funding_key(ctx.splice_parent_funding_txid)`.
	/// Used by the funding key-path partial bodies so a spliced commitment signs with
	/// the SAME rotated key the new `Q'` aggregate is built from (spec §9c).
	fn taproot_holder_funding_key(&self) -> SecretKey {
		let parent =
			self.taproot_ctx.lock().ok().and_then(|s| s.as_ref().and_then(|c| c.splice_parent_funding_txid));
		self.funding_key(parent)
	}

	fn taproot_key_agg(
		&self, secp_ctx: &Secp256k1<secp256k1::All>,
	) -> Result<(musig2::KeyAggContext, usize, usize, u64, ScriptBuf), ()> {
		let ctx = {
			let slot = self.taproot_ctx.lock().map_err(|_| ())?;
			slot.clone().ok_or(())?
		};
		// Use the ROTATED holder funding key for a spliced scope (so the aggregate is
		// the new `Q'`); the base key otherwise. The counterparty key in `ctx` is
		// already the (rotated, for a splice) one the handler supplied.
		let holder = self
			.funding_key(ctx.splice_parent_funding_txid)
			.public_key(secp_ctx)
			.serialize();
		let cp = ctx.counterparty_funding_pubkey.serialize();
		let (key_agg, our_index) =
			crate::sign::taproot_signer::channel_key_agg_ctx(&holder, &cp, &holder)
				.map_err(|_| ())?;
		let counterparty_index = 1 - our_index;
		let q = crate::sign::taproot_signer::aggregated_xonly(&key_agg);
		let spk = ScriptBuf::new_p2tr_tweaked(
			bitcoin::key::TweakedPublicKey::dangerous_assume_tweaked(q),
		);
		Ok((key_agg, our_index, counterparty_index, ctx.funding_value_sat, spk))
	}

	/// Sign the single input of `spend_tx` at index `input_idx`, which spends the output described
	/// by `descriptor`, returning the witness stack for the input.
	///
	/// Returns an error if the input at `input_idx` does not exist, has a non-empty `script_sig`,
	/// is not spending the outpoint described by [`descriptor.outpoint`],
	/// or if an output descriptor `script_pubkey` does not match the one we can spend.
	///
	/// [`descriptor.outpoint`]: StaticPaymentOutputDescriptor::outpoint
	pub fn sign_counterparty_payment_input<C: Signing>(
		&self, spend_tx: &Transaction, input_idx: usize,
		descriptor: &StaticPaymentOutputDescriptor, all_prevouts: &[bitcoin::TxOut],
		secp_ctx: &Secp256k1<C>,
	) -> Result<Witness, ()> {
		// TODO: We really should be taking the SigHashCache as a parameter here instead of
		// spend_tx, but ideally the SigHashCache would expose the transaction's inputs read-only
		// so that we can check them. This requires upstream rust-bitcoin changes (as well as
		// bindings updates to support SigHashCache objects).
		if spend_tx.input.len() <= input_idx {
			return Err(());
		}
		if !spend_tx.input[input_idx].script_sig.is_empty() {
			return Err(());
		}
		if spend_tx.input[input_idx].previous_output != descriptor.outpoint.into_bitcoin_outpoint()
		{
			return Err(());
		}

		let legacy_default_channel_type = ChannelTypeFeatures::only_static_remote_key();
		let channel_type_features = descriptor
			.channel_transaction_parameters
			.as_ref()
			.map(|params| &params.channel_type_features)
			.unwrap_or(&legacy_default_channel_type);

		let payment_point_v1 = PublicKey::from_secret_key(secp_ctx, &self.payment_key_v1);
		let payment_point_v2 = PublicKey::from_secret_key(secp_ctx, &self.payment_key_v2);

		// Simple-taproot (M9e-2): on a counterparty-broadcast commitment OUR balance is
		// the taproot `to_remote` 1-CSV tapleaf output (`<remote> OP_CHECKSIGVERIFY 1
		// OP_CSV`, spec §3), NOT a P2WSH/P2WPKH. Sweep it via the script path with a
		// BIP340 Schnorr sig over the BIP341 (Prevouts::All) script-path sighash. This is
		// the LP-side mirror of the M9e to_local/HTLC sweeps.
		if channel_type_features.supports_simple_taproot() {
			let verify_ctx = Secp256k1::verification_only();
			let spk_v1 = get_taproot_to_remote_spk(&verify_ctx, &payment_point_v1);
			let spk_v2 = get_taproot_to_remote_spk(&verify_ctx, &payment_point_v2);
			let (remote_pubkey, payment_key) = if spk_v1 == descriptor.output.script_pubkey {
				(payment_point_v1, &self.payment_key_v1)
			} else if spk_v2 == descriptor.output.script_pubkey {
				(payment_point_v2, &self.payment_key_v2)
			} else {
				return Err(());
			};
			let leaf = chan_utils::get_taproot_to_remote_script(&remote_pubkey);
			let spend_info = chan_utils::taproot_to_remote_spend_info(&verify_ctx, &remote_pubkey);
			let sighash =
				chan_utils::taproot_sweep_leaf_sighash(spend_tx, input_idx, &leaf, all_prevouts)
					.map_err(|_| ())?;
			let keypair = bitcoin::secp256k1::Keypair::from_secret_key(secp_ctx, payment_key);
			let msg = bitcoin::secp256k1::Message::from_digest(*sighash.as_ref());
			let sig = secp_ctx.sign_schnorr_no_aux_rand(&msg, &keypair);
			let elem = chan_utils::taproot_schnorr_witness_element(
				&sig,
				bitcoin::sighash::TapSighashType::Default,
			);
			return chan_utils::build_taproot_script_path_witness(elem, &leaf, &spend_info)
				.map_err(|_| ());
		}

		let spk_v1 = get_countersigner_payment_script(channel_type_features, &payment_point_v1);
		let spk_v2 = get_countersigner_payment_script(channel_type_features, &payment_point_v2);

		let (remotepubkey, payment_key) = if spk_v1 == descriptor.output.script_pubkey {
			(bitcoin::PublicKey::new(payment_point_v1), &self.payment_key_v1)
		} else {
			if spk_v2 != descriptor.output.script_pubkey {
				return Err(());
			}
			(bitcoin::PublicKey::new(payment_point_v2), &self.payment_key_v2)
		};

		let witness_script = if channel_type_features.supports_anchors_zero_fee_htlc_tx() {
			chan_utils::get_to_countersigner_keyed_anchor_redeemscript(&remotepubkey.inner)
		} else {
			ScriptBuf::new_p2pkh(&remotepubkey.pubkey_hash())
		};
		let sighash = hash_to_message!(
			&sighash::SighashCache::new(spend_tx)
				.p2wsh_signature_hash(
					input_idx,
					&witness_script,
					descriptor.output.value,
					EcdsaSighashType::All
				)
				.unwrap()[..]
		);
		let remotesig = sign_with_aux_rand(secp_ctx, &sighash, payment_key, &self);
		let payment_script = if channel_type_features.supports_anchors_zero_fee_htlc_tx() {
			witness_script.to_p2wsh()
		} else {
			ScriptBuf::new_p2wpkh(&remotepubkey.wpubkey_hash().unwrap())
		};

		if payment_script != descriptor.output.script_pubkey {
			return Err(());
		}

		let mut witness = Vec::with_capacity(2);
		witness.push(remotesig.serialize_der().to_vec());
		witness[0].push(EcdsaSighashType::All as u8);
		if channel_type_features.supports_anchors_zero_fee_htlc_tx() {
			witness.push(witness_script.to_bytes());
		} else {
			witness.push(remotepubkey.to_bytes());
		}
		Ok(witness.into())
	}

	/// Sign the single input of `spend_tx` at index `input_idx` which spends the output
	/// described by `descriptor`, returning the witness stack for the input.
	///
	/// Returns an error if the input at `input_idx` does not exist, has a non-empty `script_sig`,
	/// is not spending the outpoint described by [`descriptor.outpoint`], does not have a
	/// sequence set to [`descriptor.to_self_delay`], or if an output descriptor
	/// `script_pubkey` does not match the one we can spend.
	///
	/// [`descriptor.outpoint`]: DelayedPaymentOutputDescriptor::outpoint
	/// [`descriptor.to_self_delay`]: DelayedPaymentOutputDescriptor::to_self_delay
	pub fn sign_dynamic_p2wsh_input<C: Signing>(
		&self, spend_tx: &Transaction, input_idx: usize,
		descriptor: &DelayedPaymentOutputDescriptor, all_prevouts: &[bitcoin::TxOut],
		secp_ctx: &Secp256k1<C>,
	) -> Result<Witness, ()> {
		// TODO: We really should be taking the SigHashCache as a parameter here instead of
		// spend_tx, but ideally the SigHashCache would expose the transaction's inputs read-only
		// so that we can check them. This requires upstream rust-bitcoin changes (as well as
		// bindings updates to support SigHashCache objects).
		if spend_tx.input.len() <= input_idx {
			return Err(());
		}
		if !spend_tx.input[input_idx].script_sig.is_empty() {
			return Err(());
		}
		if spend_tx.input[input_idx].previous_output != descriptor.outpoint.into_bitcoin_outpoint()
		{
			return Err(());
		}
		if spend_tx.input[input_idx].sequence.0 != descriptor.to_self_delay as u32 {
			return Err(());
		}

		let delayed_payment_key = chan_utils::derive_private_key(
			&secp_ctx,
			&descriptor.per_commitment_point,
			&self.delayed_payment_base_key,
		);
		let delayed_payment_pubkey =
			DelayedPaymentKey::from_secret_key(&secp_ctx, &delayed_payment_key);

		// Simple-taproot (M9e) broadcaster `to_local` sweep after the CSV: spend the
		// to_delay tapleaf (`<delayed> OP_CHECKSIGVERIFY <to_self_delay> OP_CSV`) with
		// our delayed key. BIP341 script-path, SIGHASH_DEFAULT (Prevouts::All).
		let is_taproot = descriptor
			.channel_transaction_parameters
			.as_ref()
			.map(|p| p.channel_type_features.supports_simple_taproot())
			.unwrap_or(false);
		if is_taproot {
			let verify_ctx = Secp256k1::verification_only();
			let leaf = chan_utils::get_taproot_to_local_delay_script(
				descriptor.to_self_delay,
				&delayed_payment_pubkey,
			);
			let spend_info = chan_utils::taproot_to_local_spend_info(
				&verify_ctx,
				&descriptor.revocation_pubkey,
				descriptor.to_self_delay,
				&delayed_payment_pubkey,
			);
			let payment_script =
				bitcoin::ScriptBuf::new_p2tr_tweaked(spend_info.output_key());
			if descriptor.output.script_pubkey != payment_script {
				return Err(());
			}
			let sighash =
				chan_utils::taproot_sweep_leaf_sighash(spend_tx, input_idx, &leaf, all_prevouts)
					.map_err(|_| ())?;
			let keypair =
				bitcoin::secp256k1::Keypair::from_secret_key(secp_ctx, &delayed_payment_key);
			let msg = bitcoin::secp256k1::Message::from_digest(*sighash.as_ref());
			let sig = secp_ctx.sign_schnorr_no_aux_rand(&msg, &keypair);
			let elem = chan_utils::taproot_schnorr_witness_element(
				&sig,
				bitcoin::sighash::TapSighashType::Default,
			);
			return chan_utils::build_taproot_script_path_witness(elem, &leaf, &spend_info)
				.map_err(|_| ());
		}

		let witness_script = chan_utils::get_revokeable_redeemscript(
			&descriptor.revocation_pubkey,
			descriptor.to_self_delay,
			&delayed_payment_pubkey,
		);
		let sighash = hash_to_message!(
			&sighash::SighashCache::new(spend_tx)
				.p2wsh_signature_hash(
					input_idx,
					&witness_script,
					descriptor.output.value,
					EcdsaSighashType::All
				)
				.unwrap()[..]
		);
		let local_delayedsig = EcdsaSignature {
			signature: sign_with_aux_rand(secp_ctx, &sighash, &delayed_payment_key, &self),
			sighash_type: EcdsaSighashType::All,
		};
		let payment_script =
			bitcoin::Address::p2wsh(&witness_script, Network::Bitcoin).script_pubkey();

		if descriptor.output.script_pubkey != payment_script {
			return Err(());
		}

		Ok(Witness::from_slice(&[
			&local_delayedsig.serialize()[..],
			&[], // MINIMALIF
			witness_script.as_bytes(),
		]))
	}
}

impl EntropySource for InMemorySigner {
	fn get_secure_random_bytes(&self) -> [u8; 32] {
		self.entropy_source.get_secure_random_bytes()
	}
}

impl ChannelSigner for InMemorySigner {
	fn get_per_commitment_point(
		&self, idx: u64, secp_ctx: &Secp256k1<secp256k1::All>,
	) -> Result<PublicKey, ()> {
		let commitment_secret =
			SecretKey::from_slice(&chan_utils::build_commitment_secret(&self.commitment_seed, idx))
				.unwrap();
		Ok(PublicKey::from_secret_key(secp_ctx, &commitment_secret))
	}

	fn release_commitment_secret(&self, idx: u64) -> Result<[u8; 32], ()> {
		Ok(chan_utils::build_commitment_secret(&self.commitment_seed, idx))
	}

	fn validate_holder_commitment(
		&self, _holder_tx: &HolderCommitmentTransaction,
		_outbound_htlc_preimages: Vec<PaymentPreimage>,
	) -> Result<(), ()> {
		Ok(())
	}

	fn validate_counterparty_revocation(&self, _idx: u64, _secret: &SecretKey) -> Result<(), ()> {
		Ok(())
	}

	fn pubkeys(&self, secp_ctx: &Secp256k1<secp256k1::All>) -> ChannelPublicKeys {
		// Because splices always break downgrades, we go ahead and always use the new derivation
		// here as its just much better.
		let payment_key =
			if self.v2_remote_key_derivation { &self.payment_key_v2 } else { &self.payment_key_v1 };
		let from_secret = |s: &SecretKey| PublicKey::from_secret_key(secp_ctx, s);
		let pubkeys = ChannelPublicKeys {
			funding_pubkey: from_secret(&self.funding_key.0),
			revocation_basepoint: RevocationBasepoint::from(from_secret(&self.revocation_base_key)),
			payment_point: from_secret(payment_key),
			delayed_payment_basepoint: DelayedPaymentBasepoint::from(from_secret(
				&self.delayed_payment_base_key,
			)),
			htlc_basepoint: HtlcBasepoint::from(from_secret(&self.htlc_base_key)),
		};

		pubkeys
	}

	fn new_funding_pubkey(
		&self, splice_parent_funding_txid: Txid, secp_ctx: &Secp256k1<secp256k1::All>,
	) -> PublicKey {
		self.funding_key(Some(splice_parent_funding_txid)).public_key(secp_ctx)
	}

	fn channel_keys_id(&self) -> [u8; 32] {
		self.channel_keys_id
	}
}

const MISSING_PARAMS_ERR: &'static str =
	"ChannelTransactionParameters must be populated before signing operations";

impl EcdsaChannelSigner for InMemorySigner {
	fn sign_counterparty_commitment(
		&self, channel_parameters: &ChannelTransactionParameters,
		commitment_tx: &CommitmentTransaction, _inbound_htlc_preimages: Vec<PaymentPreimage>,
		_outbound_htlc_preimages: Vec<PaymentPreimage>, secp_ctx: &Secp256k1<secp256k1::All>,
	) -> Result<(Signature, Vec<Signature>), ()> {
		assert!(channel_parameters.is_populated(), "Channel parameters must be fully populated");

		let trusted_tx = commitment_tx.trust();
		let keys = trusted_tx.keys();

		let funding_key = self.funding_key(channel_parameters.splice_parent_funding_txid);
		let funding_pubkey = funding_key.public_key(secp_ctx);
		let counterparty_keys =
			channel_parameters.counterparty_pubkeys().expect(MISSING_PARAMS_ERR);
		let channel_funding_redeemscript =
			make_funding_redeemscript(&funding_pubkey, &counterparty_keys.funding_pubkey);

		let built_tx = trusted_tx.built_transaction();
		let commitment_sig = built_tx.sign_counterparty_commitment(
			&funding_key,
			&channel_funding_redeemscript,
			channel_parameters.channel_value_satoshis,
			secp_ctx,
		);
		let commitment_txid = built_tx.txid;

		let mut htlc_sigs = Vec::with_capacity(commitment_tx.nondust_htlcs().len());
		for htlc in commitment_tx.nondust_htlcs() {
			let holder_selected_contest_delay = channel_parameters.holder_selected_contest_delay;
			let chan_type = &channel_parameters.channel_type_features;
			let htlc_tx = chan_utils::build_htlc_transaction(
				&commitment_txid,
				commitment_tx.negotiated_feerate_per_kw(),
				holder_selected_contest_delay,
				htlc,
				chan_type,
				&keys.broadcaster_delayed_payment_key,
				&keys.revocation_key,
				secp_ctx,
			);
			let htlc_redeemscript = chan_utils::get_htlc_redeemscript(&htlc, chan_type, &keys);
			let htlc_sighashtype = if chan_type.supports_anchors_zero_fee_htlc_tx()
				|| chan_type.supports_anchor_zero_fee_commitments()
			{
				EcdsaSighashType::SinglePlusAnyoneCanPay
			} else {
				EcdsaSighashType::All
			};
			let htlc_sighash = hash_to_message!(
				&sighash::SighashCache::new(&htlc_tx)
					.p2wsh_signature_hash(
						0,
						&htlc_redeemscript,
						htlc.to_bitcoin_amount(),
						htlc_sighashtype
					)
					.unwrap()[..]
			);
			let holder_htlc_key = chan_utils::derive_private_key(
				&secp_ctx,
				&keys.per_commitment_point,
				&self.htlc_base_key,
			);
			htlc_sigs.push(sign(secp_ctx, &htlc_sighash, &holder_htlc_key));
		}

		Ok((commitment_sig, htlc_sigs))
	}

	fn sign_holder_commitment(
		&self, channel_parameters: &ChannelTransactionParameters,
		commitment_tx: &HolderCommitmentTransaction, secp_ctx: &Secp256k1<secp256k1::All>,
	) -> Result<Signature, ()> {
		assert!(channel_parameters.is_populated(), "Channel parameters must be fully populated");

		let funding_key = self.funding_key(channel_parameters.splice_parent_funding_txid);
		let funding_pubkey = funding_key.public_key(secp_ctx);
		let counterparty_keys =
			channel_parameters.counterparty_pubkeys().expect(MISSING_PARAMS_ERR);
		let funding_redeemscript =
			make_funding_redeemscript(&funding_pubkey, &counterparty_keys.funding_pubkey);
		let trusted_tx = commitment_tx.trust();
		Ok(trusted_tx.built_transaction().sign_holder_commitment(
			&funding_key,
			&funding_redeemscript,
			channel_parameters.channel_value_satoshis,
			&self,
			secp_ctx,
		))
	}

	#[cfg(any(test, feature = "_test_utils", feature = "unsafe_revoked_tx_signing"))]
	fn unsafe_sign_holder_commitment(
		&self, channel_parameters: &ChannelTransactionParameters,
		commitment_tx: &HolderCommitmentTransaction, secp_ctx: &Secp256k1<secp256k1::All>,
	) -> Result<Signature, ()> {
		assert!(channel_parameters.is_populated(), "Channel parameters must be fully populated");

		let funding_key = self.funding_key(channel_parameters.splice_parent_funding_txid);
		let funding_pubkey = funding_key.public_key(secp_ctx);
		let counterparty_keys =
			channel_parameters.counterparty_pubkeys().expect(MISSING_PARAMS_ERR);
		let funding_redeemscript =
			make_funding_redeemscript(&funding_pubkey, &counterparty_keys.funding_pubkey);
		let trusted_tx = commitment_tx.trust();
		Ok(trusted_tx.built_transaction().sign_holder_commitment(
			&funding_key,
			&funding_redeemscript,
			channel_parameters.channel_value_satoshis,
			&self,
			secp_ctx,
		))
	}

	fn sign_justice_revoked_output(
		&self, channel_parameters: &ChannelTransactionParameters, justice_tx: &Transaction,
		input: usize, amount: u64, per_commitment_key: &SecretKey,
		secp_ctx: &Secp256k1<secp256k1::All>,
	) -> Result<Signature, ()> {
		assert!(channel_parameters.is_populated(), "Channel parameters must be fully populated");

		let revocation_key = chan_utils::derive_private_revocation_key(
			&secp_ctx,
			&per_commitment_key,
			&self.revocation_base_key,
		);
		let per_commitment_point = PublicKey::from_secret_key(secp_ctx, &per_commitment_key);
		let revocation_pubkey = RevocationKey::from_basepoint(
			&secp_ctx,
			&channel_parameters.holder_pubkeys.revocation_basepoint,
			&per_commitment_point,
		);
		let witness_script = {
			let counterparty_keys =
				channel_parameters.counterparty_pubkeys().expect(MISSING_PARAMS_ERR);
			let holder_selected_contest_delay = channel_parameters.holder_selected_contest_delay;
			let counterparty_delayedpubkey = DelayedPaymentKey::from_basepoint(
				&secp_ctx,
				&counterparty_keys.delayed_payment_basepoint,
				&per_commitment_point,
			);
			chan_utils::get_revokeable_redeemscript(
				&revocation_pubkey,
				holder_selected_contest_delay,
				&counterparty_delayedpubkey,
			)
		};
		let mut sighash_parts = sighash::SighashCache::new(justice_tx);
		let sighash = hash_to_message!(
			&sighash_parts
				.p2wsh_signature_hash(
					input,
					&witness_script,
					Amount::from_sat(amount),
					EcdsaSighashType::All
				)
				.unwrap()[..]
		);
		return Ok(sign_with_aux_rand(secp_ctx, &sighash, &revocation_key, &self));
	}

	fn sign_justice_revoked_htlc(
		&self, channel_parameters: &ChannelTransactionParameters, justice_tx: &Transaction,
		input: usize, amount: u64, per_commitment_key: &SecretKey, htlc: &HTLCOutputInCommitment,
		secp_ctx: &Secp256k1<secp256k1::All>,
	) -> Result<Signature, ()> {
		assert!(channel_parameters.is_populated(), "Channel parameters must be fully populated");

		let revocation_key = chan_utils::derive_private_revocation_key(
			&secp_ctx,
			&per_commitment_key,
			&self.revocation_base_key,
		);
		let per_commitment_point = PublicKey::from_secret_key(secp_ctx, &per_commitment_key);
		let revocation_pubkey = RevocationKey::from_basepoint(
			&secp_ctx,
			&channel_parameters.holder_pubkeys.revocation_basepoint,
			&per_commitment_point,
		);
		let witness_script = {
			let counterparty_keys =
				channel_parameters.counterparty_pubkeys().expect(MISSING_PARAMS_ERR);
			let counterparty_htlcpubkey = HtlcKey::from_basepoint(
				&secp_ctx,
				&counterparty_keys.htlc_basepoint,
				&per_commitment_point,
			);
			let holder_htlcpubkey = HtlcKey::from_basepoint(
				&secp_ctx,
				&channel_parameters.holder_pubkeys.htlc_basepoint,
				&per_commitment_point,
			);
			chan_utils::get_htlc_redeemscript_with_explicit_keys(
				&htlc,
				&channel_parameters.channel_type_features,
				&counterparty_htlcpubkey,
				&holder_htlcpubkey,
				&revocation_pubkey,
			)
		};
		let mut sighash_parts = sighash::SighashCache::new(justice_tx);
		let sighash = hash_to_message!(
			&sighash_parts
				.p2wsh_signature_hash(
					input,
					&witness_script,
					Amount::from_sat(amount),
					EcdsaSighashType::All
				)
				.unwrap()[..]
		);
		return Ok(sign_with_aux_rand(secp_ctx, &sighash, &revocation_key, &self));
	}

	fn sign_holder_htlc_transaction(
		&self, htlc_tx: &Transaction, input: usize, htlc_descriptor: &HTLCDescriptor,
		secp_ctx: &Secp256k1<secp256k1::All>,
	) -> Result<Signature, ()> {
		let channel_parameters =
			&htlc_descriptor.channel_derivation_parameters.transaction_parameters;
		assert!(channel_parameters.is_populated(), "Channel parameters must be fully populated");

		let witness_script = htlc_descriptor.witness_script(secp_ctx);
		let sighash = &sighash::SighashCache::new(&*htlc_tx)
			.p2wsh_signature_hash(
				input,
				&witness_script,
				htlc_descriptor.htlc.to_bitcoin_amount(),
				EcdsaSighashType::All,
			)
			.map_err(|_| ())?;
		let our_htlc_private_key = chan_utils::derive_private_key(
			&secp_ctx,
			&htlc_descriptor.per_commitment_point,
			&self.htlc_base_key,
		);
		let sighash = hash_to_message!(sighash.as_byte_array());
		Ok(sign_with_aux_rand(&secp_ctx, &sighash, &our_htlc_private_key, &self))
	}

	fn sign_counterparty_htlc_transaction(
		&self, channel_parameters: &ChannelTransactionParameters, htlc_tx: &Transaction,
		input: usize, amount: u64, per_commitment_point: &PublicKey, htlc: &HTLCOutputInCommitment,
		secp_ctx: &Secp256k1<secp256k1::All>,
	) -> Result<Signature, ()> {
		assert!(channel_parameters.is_populated(), "Channel parameters must be fully populated");

		let htlc_key =
			chan_utils::derive_private_key(&secp_ctx, &per_commitment_point, &self.htlc_base_key);
		let revocation_pubkey = RevocationKey::from_basepoint(
			&secp_ctx,
			&channel_parameters.holder_pubkeys.revocation_basepoint,
			&per_commitment_point,
		);
		let counterparty_keys =
			channel_parameters.counterparty_pubkeys().expect(MISSING_PARAMS_ERR);
		let counterparty_htlcpubkey = HtlcKey::from_basepoint(
			&secp_ctx,
			&counterparty_keys.htlc_basepoint,
			&per_commitment_point,
		);
		let htlc_basepoint = channel_parameters.holder_pubkeys.htlc_basepoint;
		let htlcpubkey = HtlcKey::from_basepoint(&secp_ctx, &htlc_basepoint, &per_commitment_point);
		let chan_type = &channel_parameters.channel_type_features;
		let witness_script = chan_utils::get_htlc_redeemscript_with_explicit_keys(
			&htlc,
			chan_type,
			&counterparty_htlcpubkey,
			&htlcpubkey,
			&revocation_pubkey,
		);
		let mut sighash_parts = sighash::SighashCache::new(htlc_tx);
		let sighash = hash_to_message!(
			&sighash_parts
				.p2wsh_signature_hash(
					input,
					&witness_script,
					Amount::from_sat(amount),
					EcdsaSighashType::All
				)
				.unwrap()[..]
		);
		Ok(sign_with_aux_rand(secp_ctx, &sighash, &htlc_key, &self))
	}

	fn sign_justice_revoked_output_taproot(
		&self, channel_parameters: &ChannelTransactionParameters, justice_tx: &Transaction,
		input: usize, _amount: u64, per_commitment_key: &SecretKey, all_prevouts: &[bitcoin::TxOut],
		secp_ctx: &Secp256k1<secp256k1::All>,
	) -> Result<schnorr::Signature, ()> {
		assert!(channel_parameters.is_populated(), "Channel parameters must be fully populated");
		// Breach sweep of a revoked taproot `to_local` output via the `revoke`
		// tapleaf (`<delayed> OP_DROP <revocation> OP_CHECKSIG`) — signed by the
		// derived revocation secret. Script-path TapSighash, SIGHASH_DEFAULT.
		let revocation_key = chan_utils::derive_private_revocation_key(
			secp_ctx,
			per_commitment_key,
			&self.revocation_base_key,
		);
		let per_commitment_point = PublicKey::from_secret_key(secp_ctx, per_commitment_key);
		let revocation_pubkey = RevocationKey::from_basepoint(
			secp_ctx,
			&channel_parameters.holder_pubkeys.revocation_basepoint,
			&per_commitment_point,
		);
		let counterparty_keys = channel_parameters.counterparty_pubkeys().ok_or(())?;
		let counterparty_delayedpubkey = DelayedPaymentKey::from_basepoint(
			secp_ctx,
			&counterparty_keys.delayed_payment_basepoint,
			&per_commitment_point,
		);
		let leaf = chan_utils::get_taproot_to_local_revoke_script(
			&revocation_pubkey,
			&counterparty_delayedpubkey,
		);
		let sighash =
			chan_utils::taproot_sweep_leaf_sighash(justice_tx, input, &leaf, all_prevouts)
				.map_err(|_| ())?;
		let keypair = Keypair::from_secret_key(secp_ctx, &revocation_key);
		let msg = secp256k1::Message::from_digest(*sighash.as_ref());
		Ok(secp_ctx.sign_schnorr_no_aux_rand(&msg, &keypair))
	}

	fn sign_justice_revoked_htlc_taproot(
		&self, channel_parameters: &ChannelTransactionParameters, justice_tx: &Transaction,
		input: usize, _amount: u64, per_commitment_key: &SecretKey, htlc: &HTLCOutputInCommitment,
		all_prevouts: &[bitcoin::TxOut], secp_ctx: &Secp256k1<secp256k1::All>,
	) -> Result<schnorr::Signature, ()> {
		assert!(channel_parameters.is_populated(), "Channel parameters must be fully populated");
		// Breach sweep of a revoked taproot HTLC output. The HTLC tree's INTERNAL
		// key is the revocation key, so the breach path is a BIP341 KEY-PATH spend:
		// sign with `revocation_secret + tap_tweak(revocation_pubkey, merkle_root)`.
		let revocation_key = chan_utils::derive_private_revocation_key(
			secp_ctx,
			per_commitment_key,
			&self.revocation_base_key,
		);
		let per_commitment_point = PublicKey::from_secret_key(secp_ctx, per_commitment_key);
		let revocation_pubkey = RevocationKey::from_basepoint(
			secp_ctx,
			&channel_parameters.holder_pubkeys.revocation_basepoint,
			&per_commitment_point,
		);
		let counterparty_keys = channel_parameters.counterparty_pubkeys().ok_or(())?;
		// On the counterparty's broadcast commitment the broadcaster is the
		// counterparty; their htlc key is the broadcaster_htlc_key, ours the
		// countersignatory_htlc_key.
		let broadcaster_htlc_key = HtlcKey::from_basepoint(
			secp_ctx,
			&counterparty_keys.htlc_basepoint,
			&per_commitment_point,
		);
		let countersignatory_htlc_key = HtlcKey::from_basepoint(
			secp_ctx,
			&channel_parameters.holder_pubkeys.htlc_basepoint,
			&per_commitment_point,
		);
		let spend_info = chan_utils::taproot_htlc_spend_info(
			secp_ctx,
			htlc,
			&broadcaster_htlc_key,
			&countersignatory_htlc_key,
			&revocation_pubkey,
		);
		let sighash =
			chan_utils::taproot_sweep_keyspend_sighash(justice_tx, input, all_prevouts)
				.map_err(|_| ())?;
		let keypair = Keypair::from_secret_key(secp_ctx, &revocation_key);
		let tweak = spend_info.tap_tweak().to_scalar();
		let tweaked = keypair.add_xonly_tweak(secp_ctx, &tweak).map_err(|_| ())?;
		let msg = secp256k1::Message::from_digest(*sighash.as_ref());
		Ok(secp_ctx.sign_schnorr_no_aux_rand(&msg, &tweaked))
	}

	fn sign_holder_htlc_transaction_taproot(
		&self, htlc_tx: &Transaction, input: usize, htlc_descriptor: &HTLCDescriptor,
		secp_ctx: &Secp256k1<secp256k1::All>,
	) -> Result<schnorr::Signature, ()> {
		// Reuse the already-implemented TaprootChannelSigner body (BIP342 script-path
		// over the 2-of-2 leaf, SIGHASH_SINGLE|ANYONECANPAY, with our htlc key).
		TaprootChannelSigner::sign_holder_htlc_transaction(
			self, htlc_tx, input, htlc_descriptor, secp_ctx,
		)
	}

	fn sign_counterparty_htlc_transaction_taproot(
		&self, channel_parameters: &ChannelTransactionParameters, htlc_tx: &Transaction,
		input: usize, _amount: u64, per_commitment_point: &PublicKey, htlc: &HTLCOutputInCommitment,
		all_prevouts: &[bitcoin::TxOut], secp_ctx: &Secp256k1<secp256k1::All>,
	) -> Result<schnorr::Signature, ()> {
		assert!(channel_parameters.is_populated(), "Channel parameters must be fully populated");
		// Direct claim of an HTLC output on the COUNTERPARTY's broadcast taproot
		// commitment. We sign with OUR (countersignatory) htlc key over the leaf we
		// satisfy:
		//   offered-by-them  → success leaf (we reveal the preimage),
		//   received-by-them → timeout leaf (we reclaim after CLTV).
		// These leaves are single-sig (just our key) so the claim is a direct sweep
		// into our wallet — script-path TapSighash, SIGHASH_DEFAULT (commits all
		// prevouts + outputs, matching the legacy `EcdsaSighashType::All` claim).
		let our_htlc_secret =
			chan_utils::derive_private_key(secp_ctx, per_commitment_point, &self.htlc_base_key);
		let counterparty_keys = channel_parameters.counterparty_pubkeys().ok_or(())?;
		let _broadcaster_htlc_key = HtlcKey::from_basepoint(
			secp_ctx,
			&counterparty_keys.htlc_basepoint,
			per_commitment_point,
		);
		let countersignatory_htlc_key = HtlcKey::from_basepoint(
			secp_ctx,
			&channel_parameters.holder_pubkeys.htlc_basepoint,
			per_commitment_point,
		);
		let leaf = if htlc.offered {
			chan_utils::get_taproot_offered_htlc_success_script(
				&countersignatory_htlc_key,
				&htlc.payment_hash,
			)
		} else {
			chan_utils::get_taproot_received_htlc_timeout_script(
				&countersignatory_htlc_key,
				htlc.cltv_expiry,
			)
		};
		let sighash =
			chan_utils::taproot_sweep_leaf_sighash(htlc_tx, input, &leaf, all_prevouts)
				.map_err(|_| ())?;
		let keypair = Keypair::from_secret_key(secp_ctx, &our_htlc_secret);
		let msg = secp256k1::Message::from_digest(*sighash.as_ref());
		Ok(secp_ctx.sign_schnorr_no_aux_rand(&msg, &keypair))
	}

	fn sign_closing_transaction(
		&self, channel_parameters: &ChannelTransactionParameters, closing_tx: &ClosingTransaction,
		secp_ctx: &Secp256k1<secp256k1::All>,
	) -> Result<Signature, ()> {
		assert!(channel_parameters.is_populated(), "Channel parameters must be fully populated");

		let funding_key = self.funding_key(channel_parameters.splice_parent_funding_txid);
		let funding_pubkey = funding_key.public_key(secp_ctx);
		let counterparty_funding_key =
			&channel_parameters.counterparty_pubkeys().expect(MISSING_PARAMS_ERR).funding_pubkey;
		let channel_funding_redeemscript =
			make_funding_redeemscript(&funding_pubkey, counterparty_funding_key);
		Ok(closing_tx.trust().sign(
			&funding_key,
			&channel_funding_redeemscript,
			channel_parameters.channel_value_satoshis,
			secp_ctx,
		))
	}

	fn sign_holder_keyed_anchor_input(
		&self, chan_params: &ChannelTransactionParameters, anchor_tx: &Transaction, input: usize,
		secp_ctx: &Secp256k1<secp256k1::All>,
	) -> Result<Signature, ()> {
		assert!(chan_params.is_populated(), "Channel parameters must be fully populated");

		let witness_script =
			chan_utils::get_keyed_anchor_redeemscript(&chan_params.holder_pubkeys.funding_pubkey);
		let amt = Amount::from_sat(ANCHOR_OUTPUT_VALUE_SATOSHI);
		let sighash = sighash::SighashCache::new(&*anchor_tx)
			.p2wsh_signature_hash(input, &witness_script, amt, EcdsaSighashType::All)
			.unwrap();
		let funding_key = self.funding_key(chan_params.splice_parent_funding_txid);
		Ok(sign_with_aux_rand(secp_ctx, &hash_to_message!(&sighash[..]), &funding_key, &self))
	}

	fn sign_channel_announcement_with_funding_key(
		&self, channel_parameters: &ChannelTransactionParameters,
		msg: &UnsignedChannelAnnouncement, secp_ctx: &Secp256k1<secp256k1::All>,
	) -> Result<Signature, ()> {
		let msghash = hash_to_message!(&Sha256dHash::hash(&msg.encode()[..])[..]);
		let funding_key = self.funding_key(channel_parameters.splice_parent_funding_txid);
		Ok(secp_ctx.sign_ecdsa(&msghash, &funding_key))
	}

	fn sign_splice_shared_input(
		&self, channel_parameters: &ChannelTransactionParameters, tx: &Transaction,
		input_index: usize, secp_ctx: &Secp256k1<secp256k1::All>,
	) -> Signature {
		assert!(channel_parameters.is_populated(), "Channel parameters must be fully populated");
		assert_eq!(
			tx.input[input_index].previous_output,
			channel_parameters
				.funding_outpoint
				.as_ref()
				.expect("Funding outpoint must be known prior to signing")
				.into_bitcoin_outpoint()
		);

		let funding_key = self.funding_key(channel_parameters.splice_parent_funding_txid);
		let funding_pubkey = funding_key.public_key(secp_ctx);
		let counterparty_funding_key =
			&channel_parameters.counterparty_pubkeys().expect(MISSING_PARAMS_ERR).funding_pubkey;
		let funding_redeemscript =
			make_funding_redeemscript(&funding_pubkey, counterparty_funding_key);
		let sighash = &sighash::SighashCache::new(tx)
			.p2wsh_signature_hash(
				input_index,
				&funding_redeemscript,
				Amount::from_sat(channel_parameters.channel_value_satoshis),
				EcdsaSighashType::All,
			)
			.unwrap()[..];
		let msg = hash_to_message!(sighash);
		sign(secp_ctx, &msg, &funding_key)
	}
}

/// The base "height" domain fed to the deterministic shachain nonce derivation
/// for cooperative-close partial signatures. A close has no commitment height, so
/// we pin a sentinel range that cannot collide with any real commitment number
/// (which count *down* from `(1<<48)-1`); `u64::MAX` and the few values below it
/// are strictly above that range. Each closing **round** subtracts its index, so
/// every distinct close transaction gets a distinct nonce (spec §9f-0).
/// Mirrors `quid_ln::validating_signer::CLOSING_NONCE_BASE`.
pub const CLOSING_NONCE_BASE: u64 = u64::MAX;

/// The per-round deterministic nonce height for cooperative-close round `round`
/// (`0` = `shutdown`/first `closing_signed`). MuSig2 exchanges the nonce in round
/// 1 *before* the close fee/message is known in round 2, so the nonce CANNOT be
/// message-bound; instead we derive a FRESH nonce per round via a monotonic
/// per-round index, advertised through `shutdown_nonce` (round 0) /
/// `next_closee_nonce` (subsequent rounds). Two distinct close txs (different
/// fees) therefore never share a nonce — closing nonce reuse would otherwise
/// leak the funding private key (`docs/TAPROOT-CHANNELS-BUILD-SPEC.md` §9f-0).
/// Saturates so a pathological round count cannot wrap into the commitment range.
pub const fn closing_nonce_height(round: u64) -> u64 {
	CLOSING_NONCE_BASE.saturating_sub(round)
}

/// The deterministic shachain nonce **height** for the MuSig2 partial that signs a
/// splice transaction's shared (old-funding) input, derived from the
/// `prev_funding_txid` it spends (`docs/TAPROOT-CHANNELS-BUILD-SPEC.md` §9c/§9f-0).
///
/// ## Why per-`prev_funding_txid` — and the RBF caveat (the §9f-0 lesson)
/// A channel can splice MANY times over its life; each splice signs a DIFFERENT
/// splice tx (different sighash message `m`). If two splice partials reused the same
/// nonce `k` over `m1 ≠ m2`, the counterparty could solve `x = (s1−s2)/(e1−e2)` for
/// our funding private key — the exact closing-nonce-reuse leak fixed in §9f-0. Each
/// DISTINCT splice spends a distinct prior funding output (`prev_funding_txid` is
/// unique per splice and re-derivable from chain state, so this is crash-safe), so
/// keying on it separates the nonces of two *distinct* splices. The advertised splice
/// nonce (`splice_init`/`splice_ack` `splice_nonce`) is derived at this same height,
/// so the advertised nonce equals the one we sign with.
///
/// ⚠️ CAVEAT — this does NOT cover RBF of a splice: an RBF replacement spends the
/// SAME `prev_funding_txid` with a DIFFERENT message, so it would re-derive the SAME
/// nonce height over a different `m` — a direct reuse leak. Today that is unreachable
/// because (a) `tx_init_rbf`/`tx_ack_rbf` are rejected (dual-funding disabled), (b) a
/// reconnect retransmit REPLAYS the cached partial rather than re-signing, and (c) the
/// `bind_nonce` reuse guard refuses re-signing this nonce against a different `m`
/// within a process. BEFORE enabling splice RBF, this height MUST gain a per-attempt
/// monotonic component (like `closing_round`), persisted, or the secret nonce must be
/// message-bound — otherwise (c) alone is defeated by a host-restart (SGX) that resets
/// the guard between the two RBF signings.
///
/// ## Disjoint height domain (no collision with commitment / closing nonces)
/// Commitment numbers count DOWN from `(1<<48)−1`, so they live in `[0, 2^48)`.
/// Closing nonces live near the top (`u64::MAX − round`). We map the txid into the
/// strictly disjoint window `[2^48, 2^56)`, so a splice nonce can never collide with
/// a commitment-height or closing-round nonce on the same shachain root.
pub fn splice_nonce_height(prev_funding_txid: &Txid) -> u64 {
	let mut eng = Sha256::engine();
	eng.input(b"quid-taproot-splice-nonce");
	eng.input(prev_funding_txid.as_byte_array());
	let h = Sha256::from_engine(eng).to_byte_array();
	let mut x = [0u8; 8];
	x.copy_from_slice(&h[..8]);
	let raw = u64::from_be_bytes(x);
	// Fold into the 56-bit window then shift it above the commitment range:
	// result ∈ [2^48, 2^48 + 2^56) ⊂ [2^48, 2^56 + 2^48), strictly below the
	// closing range (top of u64) and strictly above the commitment range (<2^48).
	(1u64 << 48).wrapping_add(raw & ((1u64 << 56) - 1))
}

// MuSig2 key-path signer for simple taproot channels (spec §1/§2/§5). The funding
// key-path partial needs (a) the counterparty funding pubkey to build the
// per-channel `KeyAggContext` (→ the `0x5120||Q` funding scriptPubKey + funding
// amount the BIP341 key-path sighash commits to), supplied by the nonce-exchange
// handler as a late-bound `TaprootSignerContext`, and (b) the counterparty
// nonce / partial driving the 2-party round. The deterministic per-height JIT
// signing nonce + partial-sign + aggregate run through `crate::sign::taproot_signer`.
// HTLC justice/sign methods stay `todo!("M6-HTLC")` (a no-HTLC channel is valid).
impl TaprootChannelSigner for InMemorySigner {
	fn provide_taproot_context(&self, ctx: TaprootSignerContext) {
		// Same body as the inherent `InMemorySigner::provide_taproot_context`;
		// exposed through the trait so the generic nonce-exchange handler can
		// supply the context via `ChannelSignerType::as_taproot()`.
		if let Ok(mut slot) = self.taproot_ctx.lock() {
			*slot = Some(ctx);
		}
	}

	fn generate_local_nonce_pair(
		&self, commitment_number: u64, secp_ctx: &Secp256k1<All>,
	) -> PublicNonce {
		let (key_agg, our_index, _cp_index, _value, _spk) = self
			.taproot_key_agg(secp_ctx)
			.expect("taproot context must be supplied before advertising a nonce");
		crate::sign::taproot_signer::local_pubnonce(
			key_agg,
			our_index,
			&self.commitment_seed,
			commitment_number,
		)
		.expect("local nonce derivation")
	}

	fn partially_sign_counterparty_commitment(
		&self, counterparty_nonce: PublicNonce, commitment_tx: &CommitmentTransaction,
		_inbound_htlc_preimages: Vec<PaymentPreimage>,
		_outbound_htlc_preimages: Vec<PaymentPreimage>, secp_ctx: &Secp256k1<All>,
	) -> Result<(PartialSignatureWithNonce, Vec<schnorr::Signature>), ()> {
		let idx = commitment_tx.commitment_number();
		let (key_agg, our_index, counterparty_index, funding_value_sat, funding_spk) =
			self.taproot_key_agg(secp_ctx)?;

		let built = commitment_tx.trust();
		let tx = &built.built_transaction().transaction;
		let sighash = chan_utils::taproot_funding_keyspend_sighash(
			tx,
			0,
			Amount::from_sat(funding_value_sat),
			&funding_spk,
		)
		.map_err(|_| ())?;
		let message: [u8; 32] = *sighash.as_ref();

		// Counterparty commitment: domain-separated nonce so it can never equal the
		// holder-commitment nonce at this same `idx` (both numbers count down from
		// INITIAL_COMMITMENT_NUMBER in lockstep) — reusing it across the two
		// different commitment sighashes would leak the funding key.
		let (partial, our_pubnonce) =
			crate::sign::taproot_signer::our_key_path_partial_counterparty(
				key_agg,
				our_index,
				counterparty_index,
				self.taproot_holder_funding_key(),
				&self.commitment_seed,
				idx,
				counterparty_nonce,
				message,
			)
			.map_err(|_| ())?;

		// HTLC sigs (spec §3, M9b): one BIP340 Schnorr sig per non-dust HTLC over
		// the second-level HTLC tx, signed with OUR htlc base key. The broadcaster
		// of the counterparty commitment is the counterparty, so the delay is
		// `to_broadcaster_delay`.
		let contest_delay = built.to_broadcaster_delay().unwrap_or(0);
		let htlc_sigs = chan_utils::taproot_counterparty_commitment_htlc_sigs(
			commitment_tx,
			&self.htlc_base_key,
			contest_delay,
			secp_ctx,
		)
		.map_err(|_| ())?;

		Ok((PartialSignatureWithNonce(partial, our_pubnonce), htlc_sigs))
	}

	fn finalize_holder_commitment(
		&self, commitment_tx: &HolderCommitmentTransaction,
		counterparty_partial_signature: PartialSignatureWithNonce, secp_ctx: &Secp256k1<All>,
	) -> Result<PartialSignature, ()> {
		let idx = commitment_tx.commitment_number();
		let (key_agg, our_index, counterparty_index, funding_value_sat, funding_spk) =
			self.taproot_key_agg(secp_ctx)?;

		let built = commitment_tx.trust();
		let tx = &built.built_transaction().transaction;
		let sighash = chan_utils::taproot_funding_keyspend_sighash(
			tx,
			0,
			Amount::from_sat(funding_value_sat),
			&funding_spk,
		)
		.map_err(|_| ())?;
		let message: [u8; 32] = *sighash.as_ref();

		let PartialSignatureWithNonce(_cp_partial, cp_nonce) = counterparty_partial_signature;
		let (partial, _our_pubnonce) = crate::sign::taproot_signer::our_key_path_partial(
			key_agg,
			our_index,
			counterparty_index,
			self.taproot_holder_funding_key(),
			&self.commitment_seed,
			idx,
			cp_nonce,
			message,
		)
		.map_err(|_| ())?;
		Ok(partial)
	}

	fn sign_justice_revoked_output(
		&self, _justice_tx: &Transaction, _input: usize, _amount: u64,
		_per_commitment_key: &SecretKey, _secp_ctx: &Secp256k1<All>,
	) -> Result<schnorr::Signature, ()> {
		// Breach sweep of a revoked counterparty `to_local` output (script-path
		// `revoke` leaf). The exact tapleaf hash needs the counterparty's delayed
		// key, which this trait method does not pass (no `channel_parameters`); the
		// production breach-sweep path supplies it through the `ChannelMonitor`
		// descriptor (M9 force-close-sweep slice), not through `InMemorySigner`.
		// This happy-swap-path signer therefore declines the breach sweep rather
		// than emit a sig over an incomplete message.
		Err(())
	}

	fn sign_justice_revoked_htlc(
		&self, _justice_tx: &Transaction, _input: usize, _amount: u64,
		_per_commitment_key: &SecretKey, _htlc: &HTLCOutputInCommitment, _secp_ctx: &Secp256k1<All>,
	) -> Result<schnorr::Signature, ()> {
		// Breach sweep of a revoked HTLC output (internal key = revocation_pubkey →
		// key-path spend). The key-path TapSighash commits to the exact prevout
		// scriptPubKey (`0x5120 || revocation_output_key`), which needs the HTLC's
		// htlc keys to reconstruct — not passed by this trait method. The monitor
		// descriptor path supplies it (M9 force-close-sweep slice).
		Err(())
	}

	fn sign_holder_htlc_transaction(
		&self, htlc_tx: &Transaction, input: usize, htlc_descriptor: &HTLCDescriptor,
		secp_ctx: &Secp256k1<All>,
	) -> Result<schnorr::Signature, ()> {
		// Our second-level HTLC-Success/Timeout tx spends the holder commitment's
		// HTLC output via the 2-of-2 leaf. Sign a BIP342 script-path TapSighash
		// (SIGHASH_SINGLE|ANYONECANPAY) with our per-commitment HTLC key (spec §3).
		let channel_parameters =
			&htlc_descriptor.channel_derivation_parameters.transaction_parameters;
		let directed = channel_parameters.as_holder_broadcastable();
		let keys = chan_utils::TxCreationKeys::from_channel_static_keys(
			&htlc_descriptor.per_commitment_point,
			directed.broadcaster_pubkeys(),
			directed.countersignatory_pubkeys(),
			secp_ctx,
		);
		let sighash = chan_utils::taproot_resolution_htlc_sighash(
			secp_ctx,
			htlc_tx,
			input,
			htlc_descriptor.htlc.to_bitcoin_amount(),
			&htlc_descriptor.htlc,
			&keys.broadcaster_htlc_key,
			&keys.countersignatory_htlc_key,
			&keys.revocation_key,
		)
		.map_err(|_| ())?;
		let our_htlc_secret = chan_utils::derive_private_key(
			secp_ctx,
			&htlc_descriptor.per_commitment_point,
			&self.htlc_base_key,
		);
		let keypair = bitcoin::secp256k1::Keypair::from_secret_key(secp_ctx, &our_htlc_secret);
		let msg = secp256k1::Message::from_digest(*sighash.as_ref());
		Ok(secp_ctx.sign_schnorr_no_aux_rand(&msg, &keypair))
	}

	fn sign_counterparty_htlc_transaction(
		&self, _htlc_tx: &Transaction, _input: usize, _amount: u64,
		_per_commitment_point: &PublicKey, _htlc: &HTLCOutputInCommitment, _secp_ctx: &Secp256k1<All>,
	) -> Result<schnorr::Signature, ()> {
		// Claim an HTLC output on the counterparty's broadcast commitment via the
		// 2-of-2 leaf. The leaf hash needs BOTH htlc keys (counterparty broadcaster
		// + our countersignatory) and the revocation pubkey; this trait method does
		// not pass `channel_parameters`, so the counterparty's htlc basepoint is not
		// available here. The production on-chain-claim path supplies the full key
		// set via the monitor descriptor (M9 force-close-sweep slice); this signer
		// declines rather than sign over an incomplete leaf.
		Err(())
	}

	fn partially_sign_closing_transaction(
		&self, closing_tx: &ClosingTransaction, secp_ctx: &Secp256k1<All>,
	) -> Result<PartialSignature, ()> {
		let (key_agg, our_index, counterparty_index, funding_value_sat, funding_spk) =
			self.taproot_key_agg(secp_ctx)?;
		// Per-round closing nonce: the secret nonce is derived at
		// `closing_nonce_height(closing_round)`, NOT a fixed sentinel, so two
		// distinct close txs (different fees) never share a nonce (spec §9f-0).
		let (cp_nonce, closing_round) = {
			let slot = self.taproot_ctx.lock().map_err(|_| ())?;
			let ctx = slot.as_ref().ok_or(())?;
			(ctx.counterparty_closing_nonce.clone().ok_or(())?, ctx.closing_round)
		};

		let built = closing_tx.trust();
		let tx = built.built_transaction();
		let sighash = chan_utils::taproot_funding_keyspend_sighash(
			tx,
			0,
			Amount::from_sat(funding_value_sat),
			&funding_spk,
		)
		.map_err(|_| ())?;
		let message: [u8; 32] = *sighash.as_ref();

		let (partial, _our_pubnonce) = crate::sign::taproot_signer::our_key_path_partial(
			key_agg,
			our_index,
			counterparty_index,
			self.taproot_holder_funding_key(),
			&self.commitment_seed,
			closing_nonce_height(closing_round),
			cp_nonce,
			message,
		)
		.map_err(|_| ())?;
		Ok(partial)
	}

	fn generate_splice_nonce(
		&self, prev_funding_txid: &bitcoin::Txid, secp_ctx: &Secp256k1<All>,
	) -> Option<PublicNonce> {
		// The splice signs the OLD (current) funding output, so the KeyAggContext is
		// built from the CURRENT funding keys (the OLD `Q`), exactly as the closing /
		// commitment partials do — `funding_key(None)` / `pubkeys().funding_pubkey`.
		let (key_agg, our_index, _cp, _value, _spk) = self.taproot_key_agg(secp_ctx).ok()?;
		crate::sign::taproot_signer::local_pubnonce(
			key_agg,
			our_index,
			&self.commitment_seed,
			crate::sign::splice_nonce_height(prev_funding_txid),
		)
		.ok()
	}

	fn partially_sign_splice_shared_input(
		&self, tx: &Transaction, input_index: usize, all_prevouts: &[bitcoin::TxOut],
		counterparty_nonce: PublicNonce, prev_funding_txid: &bitcoin::Txid,
		secp_ctx: &Secp256k1<All>,
	) -> Result<(PartialSignature, PublicNonce), ()> {
		// The splice tx spends the OLD funding output (the current `0x5120||Q`); the
		// KeyAggContext is the CURRENT funding-key aggregate (spec §9c). A splice tx
		// has MULTIPLE inputs, so the BIP341 key-path sighash must commit to ALL
		// prevouts (`Prevouts::All`), unlike the single-input commitment/close paths.
		let (key_agg, our_index, counterparty_index, _value, _spk) =
			self.taproot_key_agg(secp_ctx)?;
		let sighash = chan_utils::taproot_splice_keyspend_sighash(tx, input_index, all_prevouts)
			.map_err(|_| ())?;
		let message: [u8; 32] = *sighash.as_ref();
		crate::sign::taproot_signer::our_key_path_partial(
			key_agg,
			our_index,
			counterparty_index,
			self.taproot_holder_funding_key(),
			&self.commitment_seed,
			crate::sign::splice_nonce_height(prev_funding_txid),
			counterparty_nonce,
			message,
		)
		.map_err(|_| ())
	}
}

/// Simple implementation of [`EntropySource`], [`NodeSigner`], and [`SignerProvider`] that takes a
/// 32-byte seed for use as a BIP 32 extended key and derives keys from that.
///
/// Your `node_id` is seed/0'.
/// Unilateral closes may use seed/1'.
/// Cooperative closes may use seed/2'.
/// The two close keys may be needed to claim on-chain funds!
///
/// This struct cannot be used for nodes that wish to support receiving phantom payments;
/// [`PhantomKeysManager`] must be used instead.
///
/// Note that switching between this struct and [`PhantomKeysManager`] will invalidate any
/// previously issued invoices and attempts to pay previous invoices will fail.
pub struct KeysManager {
	secp_ctx: Secp256k1<secp256k1::All>,
	node_secret: SecretKey,
	node_id: PublicKey,
	inbound_payment_key: ExpandedKey,
	destination_script: ScriptBuf,
	shutdown_pubkey: PublicKey,
	channel_master_key: Xpriv,
	static_payment_key: Xpriv,
	v2_remote_key_derivation: bool,
	channel_child_index: AtomicUsize,
	peer_storage_key: PeerStorageKey,
	receive_auth_key: ReceiveAuthKey,

	#[cfg(test)]
	pub(crate) entropy_source: RandomBytes,
	#[cfg(not(test))]
	entropy_source: RandomBytes,

	seed: [u8; 32],
	starting_time_secs: u64,
	starting_time_nanos: u32,
}

impl KeysManager {
	/// Constructs a [`KeysManager`] from a 32-byte seed. If the seed is in some way biased (e.g.,
	/// your CSRNG is busted) this may panic (but more importantly, you will possibly lose funds).
	/// `starting_time` isn't strictly required to actually be a time, but it must absolutely,
	/// without a doubt, be unique to this instance. ie if you start multiple times with the same
	/// `seed`, `starting_time` must be unique to each run. Thus, the easiest way to achieve this
	/// is to simply use the current time (with very high precision).
	///
	/// The `seed` MUST be backed up safely prior to use so that the keys can be re-created, however,
	/// obviously, `starting_time` should be unique every time you reload the library - it is only
	/// used to generate new ephemeral key data (which will be stored by the individual channel if
	/// necessary).
	///
	/// Note that the seed is required to recover certain on-chain funds independent of
	/// [`ChannelMonitor`] data, though a current copy of [`ChannelMonitor`] data is also required
	/// for any channel, and some on-chain during-closing funds.
	///
	/// If `v2_remote_key_derivation` is set, the `script_pubkey`s which receive funds on-chain when
	/// our counterparty force-closes will be one of a static set of [`STATIC_PAYMENT_KEY_COUNT`]*2
	/// possible `script_pubkey`s. This only applies to new or spliced channels, however if this is
	/// set you *MUST NOT* downgrade to a version of LDK prior to 0.2.
	///
	/// [`ChannelMonitor`]: crate::chain::channelmonitor::ChannelMonitor
	pub fn new(
		seed: &[u8; 32], starting_time_secs: u64, starting_time_nanos: u32,
		v2_remote_key_derivation: bool,
	) -> Self {
		// Constants for key derivation path indices used in this function.
		const NODE_SECRET_INDEX: ChildNumber = ChildNumber::Hardened { index: 0 };
		const DESTINATION_SCRIPT_INDEX: ChildNumber = ChildNumber::Hardened { index: 1 };
		const SHUTDOWN_PUBKEY_INDEX: ChildNumber = ChildNumber::Hardened { index: 2 };
		const CHANNEL_MASTER_KEY_INDEX: ChildNumber = ChildNumber::Hardened { index: 3 };
		const INBOUND_PAYMENT_KEY_INDEX: ChildNumber = ChildNumber::Hardened { index: 5 };
		const PEER_STORAGE_KEY_INDEX: ChildNumber = ChildNumber::Hardened { index: 6 };
		const RECEIVE_AUTH_KEY_INDEX: ChildNumber = ChildNumber::Hardened { index: 7 };
		const STATIC_PAYMENT_KEY_INDEX: ChildNumber = ChildNumber::Hardened { index: 8 };

		let secp_ctx = Secp256k1::new();
		// Note that when we aren't serializing the key, network doesn't matter
		match Xpriv::new_master(Network::Testnet, seed) {
			Ok(master_key) => {
				let node_secret = master_key
					.derive_priv(&secp_ctx, &NODE_SECRET_INDEX)
					.expect("Your RNG is busted")
					.private_key;
				let node_id = PublicKey::from_secret_key(&secp_ctx, &node_secret);
				let destination_script =
					match master_key.derive_priv(&secp_ctx, &DESTINATION_SCRIPT_INDEX) {
						Ok(destination_key) => {
							let wpubkey_hash = WPubkeyHash::hash(
								&Xpub::from_priv(&secp_ctx, &destination_key).to_pub().to_bytes(),
							);
							Builder::new()
								.push_opcode(opcodes::all::OP_PUSHBYTES_0)
								.push_slice(&wpubkey_hash.to_byte_array())
								.into_script()
						},
						Err(_) => panic!("Your RNG is busted"),
					};
				let shutdown_pubkey =
					match master_key.derive_priv(&secp_ctx, &SHUTDOWN_PUBKEY_INDEX) {
						Ok(shutdown_key) => Xpub::from_priv(&secp_ctx, &shutdown_key).public_key,
						Err(_) => panic!("Your RNG is busted"),
					};
				let channel_master_key = master_key
					.derive_priv(&secp_ctx, &CHANNEL_MASTER_KEY_INDEX)
					.expect("Your RNG is busted");
				let inbound_payment_key: SecretKey = master_key
					.derive_priv(&secp_ctx, &INBOUND_PAYMENT_KEY_INDEX)
					.expect("Your RNG is busted")
					.private_key;
				let mut inbound_pmt_key_bytes = [0; 32];
				inbound_pmt_key_bytes.copy_from_slice(&inbound_payment_key[..]);
				let peer_storage_key = master_key
					.derive_priv(&secp_ctx, &PEER_STORAGE_KEY_INDEX)
					.expect("Your RNG is busted")
					.private_key;

				let receive_auth_key = master_key
					.derive_priv(&secp_ctx, &RECEIVE_AUTH_KEY_INDEX)
					.expect("Your RNG is busted")
					.private_key;

				let static_payment_key = master_key
					.derive_priv(&secp_ctx, &STATIC_PAYMENT_KEY_INDEX)
					.expect("Your RNG is busted");

				let mut rand_bytes_engine = Sha256::engine();
				rand_bytes_engine.input(&starting_time_secs.to_be_bytes());
				rand_bytes_engine.input(&starting_time_nanos.to_be_bytes());
				rand_bytes_engine.input(seed);
				rand_bytes_engine.input(b"LDK PRNG Seed");
				let rand_bytes_unique_start =
					Sha256::from_engine(rand_bytes_engine).to_byte_array();

				let mut res = KeysManager {
					secp_ctx,
					node_secret,
					node_id,
					inbound_payment_key: ExpandedKey::new(inbound_pmt_key_bytes),

					peer_storage_key: PeerStorageKey { inner: peer_storage_key.secret_bytes() },
					receive_auth_key: ReceiveAuthKey(receive_auth_key.secret_bytes()),

					destination_script,
					shutdown_pubkey,

					channel_master_key,
					channel_child_index: AtomicUsize::new(0),

					static_payment_key,
					v2_remote_key_derivation,

					entropy_source: RandomBytes::new(rand_bytes_unique_start),

					seed: *seed,
					starting_time_secs,
					starting_time_nanos,
				};
				let secp_seed = res.get_secure_random_bytes();
				res.secp_ctx.seeded_randomize(&secp_seed);
				res
			},
			Err(_) => panic!("Your rng is busted"),
		}
	}

	/// Gets the "node_id" secret key used to sign gossip announcements, decode onion data, etc.
	pub fn get_node_secret_key(&self) -> SecretKey {
		self.node_secret
	}

	/// Gets the set of possible `script_pubkey`s which can appear on chain for our
	/// non-HTLC-encumbered balance if our counterparty force-closes a channel.
	///
	/// If you've lost all data except your seed, asking your peers nicely to force-close the
	/// chanels they had with you (and hoping they don't broadcast a stale state and that there are
	/// no pending HTLCs in the latest state) and scanning the chain for these `script_pubkey`s can
	/// allow you to recover (some of) your funds.
	///
	/// Only channels opened when using a [`KeysManager`] with the `v2_remote_key_derivation`
	/// argument to [`KeysManager::new`] set, or any spliced channels will close to such scripts,
	/// other channels will close to a randomly-generated `script_pubkey`.
	pub fn possible_v2_counterparty_closed_balance_spks<C: Signing>(
		&self, secp_ctx: &Secp256k1<C>,
	) -> Vec<ScriptBuf> {
		let mut res = Vec::with_capacity(usize::from(STATIC_PAYMENT_KEY_COUNT) * 2);
		let static_remote_key_features = ChannelTypeFeatures::only_static_remote_key();
		let mut zero_fee_htlc_features = ChannelTypeFeatures::only_static_remote_key();
		zero_fee_htlc_features.set_anchors_zero_fee_htlc_tx_required();
		for idx in 0..STATIC_PAYMENT_KEY_COUNT {
			let key = self
				.static_payment_key
				.derive_priv(
					&self.secp_ctx,
					&ChildNumber::from_hardened_idx(u32::from(idx)).expect("key space exhausted"),
				)
				.expect("Your RNG is busted")
				.private_key;
			let pubkey = PublicKey::from_secret_key(secp_ctx, &key);
			res.push(get_countersigner_payment_script(&static_remote_key_features, &pubkey));
			res.push(get_countersigner_payment_script(&zero_fee_htlc_features, &pubkey));
		}
		res
	}

	fn derive_payment_key_v2(&self, key_idx: u64) -> SecretKey {
		let idx = key_idx % u64::from(STATIC_PAYMENT_KEY_COUNT);
		self.static_payment_key
			.derive_priv(
				&self.secp_ctx,
				&ChildNumber::from_hardened_idx(idx as u32).expect("key space exhausted"),
			)
			.expect("Your RNG is busted")
			.private_key
	}

	/// Derive an old [`EcdsaChannelSigner`] containing per-channel secrets based on a key derivation parameters.
	pub fn derive_channel_keys(&self, params: &[u8; 32]) -> InMemorySigner {
		let chan_id = u64::from_be_bytes(params[0..8].try_into().unwrap());
		let mut unique_start = Sha256::engine();
		unique_start.input(params);
		unique_start.input(&self.seed);

		// We only seriously intend to rely on the channel_master_key for true secure
		// entropy, everything else just ensures uniqueness. We rely on the unique_start (ie
		// starting_time provided in the constructor) to be unique.
		let child_privkey = self
			.channel_master_key
			.derive_priv(
				&self.secp_ctx,
				&ChildNumber::from_hardened_idx((chan_id as u32) % (1 << 31))
					.expect("key space exhausted"),
			)
			.expect("Your RNG is busted");
		unique_start.input(&child_privkey.private_key[..]);

		let seed = Sha256::from_engine(unique_start).to_byte_array();

		let commitment_seed = {
			let mut sha = Sha256::engine();
			sha.input(&seed);
			sha.input(&b"commitment seed"[..]);
			Sha256::from_engine(sha).to_byte_array()
		};
		macro_rules! key_step {
			($info: expr, $prev_key: expr) => {{
				let mut sha = Sha256::engine();
				sha.input(&seed);
				sha.input(&$prev_key[..]);
				sha.input(&$info[..]);
				SecretKey::from_slice(&Sha256::from_engine(sha).to_byte_array())
					.expect("SHA-256 is busted")
			}};
		}
		let funding_key = key_step!(b"funding key", commitment_seed);
		let revocation_base_key = key_step!(b"revocation base key", funding_key);
		let payment_key_v1 = key_step!(b"payment key", revocation_base_key);
		let delayed_payment_base_key = key_step!(b"delayed payment base key", payment_key_v1);
		let htlc_base_key = key_step!(b"HTLC base key", delayed_payment_base_key);
		let prng_seed = self.get_secure_random_bytes();

		let payment_key_v2_idx =
			u64::from_le_bytes(commitment_seed[..8].try_into().expect("8 bytes"));

		InMemorySigner::new(
			funding_key,
			revocation_base_key,
			payment_key_v1,
			self.derive_payment_key_v2(payment_key_v2_idx),
			self.v2_remote_key_derivation,
			delayed_payment_base_key,
			htlc_base_key,
			commitment_seed,
			params.clone(),
			prng_seed,
		)
	}

	/// Signs the given [`Psbt`] which spends the given [`SpendableOutputDescriptor`]s.
	/// The resulting inputs will be finalized and the PSBT will be ready for broadcast if there
	/// are no other inputs that need signing.
	///
	/// Returns `Err(())` if the PSBT is missing a descriptor or if we fail to sign.
	///
	/// May panic if the [`SpendableOutputDescriptor`]s were not generated by channels which used
	/// this [`KeysManager`] or one of the [`InMemorySigner`] created by this [`KeysManager`].
	pub fn sign_spendable_outputs_psbt<C: Signing>(
		&self, descriptors: &[&SpendableOutputDescriptor], mut psbt: Psbt, secp_ctx: &Secp256k1<C>,
	) -> Result<Psbt, ()> {
		let mut keys_cache: Option<(InMemorySigner, [u8; 32])> = None;
		// BIP341 script-path TapSighash for a taproot `to_local` delayed-output sweep
		// (M9e) and the `to_remote` static-payment sweep (M9e-2) both commit to ALL
		// prevouts (`Prevouts::All`); gather them in tx-input order from the PSBT's
		// witness_utxos (set by `to_psbt_input` for every descriptor).
		let all_prevouts: Vec<TxOut> = psbt
			.inputs
			.iter()
			.map(|i| i.witness_utxo.clone().unwrap_or(TxOut {
				value: Amount::ZERO,
				script_pubkey: ScriptBuf::new(),
			}))
			.collect();
		for outp in descriptors {
			let get_input_idx = |outpoint: &OutPoint| {
				psbt.unsigned_tx
					.input
					.iter()
					.position(|i| i.previous_output == outpoint.into_bitcoin_outpoint())
					.ok_or(())
			};
			match outp {
				SpendableOutputDescriptor::StaticPaymentOutput(descriptor) => {
					let input_idx = get_input_idx(&descriptor.outpoint)?;
					if keys_cache.is_none()
						|| keys_cache.as_ref().unwrap().1 != descriptor.channel_keys_id
					{
						let signer = self.derive_channel_keys(&descriptor.channel_keys_id);
						keys_cache = Some((signer, descriptor.channel_keys_id));
					}
					#[cfg(test)]
					if self.v2_remote_key_derivation {
						// In tests, we don't have to deal with upgrades from V1 signers with
						// `v2_remote_key_derivation` set, so use this opportunity to test
						// `possible_v2_counterparty_closed_balance_spks`.
						let possible_spks =
							self.possible_v2_counterparty_closed_balance_spks(secp_ctx);
						assert!(possible_spks.contains(&descriptor.output.script_pubkey));
					}
					let witness = keys_cache.as_ref().unwrap().0.sign_counterparty_payment_input(
						&psbt.unsigned_tx,
						input_idx,
						&descriptor,
						&all_prevouts,
						&secp_ctx,
					)?;
					psbt.inputs[input_idx].final_script_witness = Some(witness);
				},
				SpendableOutputDescriptor::DelayedPaymentOutput(descriptor) => {
					let input_idx = get_input_idx(&descriptor.outpoint)?;
					if keys_cache.is_none()
						|| keys_cache.as_ref().unwrap().1 != descriptor.channel_keys_id
					{
						keys_cache = Some((
							self.derive_channel_keys(&descriptor.channel_keys_id),
							descriptor.channel_keys_id,
						));
					}
					let witness = keys_cache.as_ref().unwrap().0.sign_dynamic_p2wsh_input(
						&psbt.unsigned_tx,
						input_idx,
						&descriptor,
						&all_prevouts,
						&secp_ctx,
					)?;
					psbt.inputs[input_idx].final_script_witness = Some(witness);
				},
				SpendableOutputDescriptor::StaticOutput { ref outpoint, ref output, .. } => {
					let input_idx = get_input_idx(outpoint)?;
					let derivation_idx =
						if output.script_pubkey == self.destination_script { 1 } else { 2 };
					let secret = {
						// Note that when we aren't serializing the key, network doesn't matter
						match Xpriv::new_master(Network::Testnet, &self.seed) {
							Ok(master_key) => {
								match master_key.derive_priv(
									&secp_ctx,
									&ChildNumber::from_hardened_idx(derivation_idx)
										.expect("key space exhausted"),
								) {
									Ok(key) => key,
									Err(_) => panic!("Your RNG is busted"),
								}
							},
							Err(_) => panic!("Your rng is busted"),
						}
					};
					let pubkey = Xpub::from_priv(&secp_ctx, &secret).to_pub();
					if derivation_idx == 2 {
						assert_eq!(pubkey.0, self.shutdown_pubkey);
					}
					let witness_script =
						bitcoin::Address::p2pkh(&pubkey, Network::Testnet).script_pubkey();
					let payment_script =
						bitcoin::Address::p2wpkh(&pubkey, Network::Testnet).script_pubkey();

					if payment_script != output.script_pubkey {
						return Err(());
					};

					let sighash = hash_to_message!(
						&sighash::SighashCache::new(&psbt.unsigned_tx)
							.p2wsh_signature_hash(
								input_idx,
								&witness_script,
								output.value,
								EcdsaSighashType::All
							)
							.unwrap()[..]
					);
					let sig = sign_with_aux_rand(secp_ctx, &sighash, &secret.private_key, &self);
					let mut sig_ser = sig.serialize_der().to_vec();
					sig_ser.push(EcdsaSighashType::All as u8);
					let witness = Witness::from_slice(&[&sig_ser, &pubkey.0.serialize().to_vec()]);
					psbt.inputs[input_idx].final_script_witness = Some(witness);
				},
			}
		}

		Ok(psbt)
	}
}

impl EntropySource for KeysManager {
	fn get_secure_random_bytes(&self) -> [u8; 32] {
		self.entropy_source.get_secure_random_bytes()
	}
}

impl NodeSigner for KeysManager {
	fn get_node_id(&self, recipient: Recipient) -> Result<PublicKey, ()> {
		match recipient {
			Recipient::Node => Ok(self.node_id.clone()),
			Recipient::PhantomNode => Err(()),
		}
	}

	fn ecdh(
		&self, recipient: Recipient, other_key: &PublicKey, tweak: Option<&Scalar>,
	) -> Result<SharedSecret, ()> {
		let mut node_secret = match recipient {
			Recipient::Node => Ok(self.node_secret.clone()),
			Recipient::PhantomNode => Err(()),
		}?;
		if let Some(tweak) = tweak {
			node_secret = node_secret.mul_tweak(tweak).map_err(|_| ())?;
		}
		Ok(SharedSecret::new(other_key, &node_secret))
	}

	fn get_expanded_key(&self) -> ExpandedKey {
		self.inbound_payment_key.clone()
	}

	fn get_peer_storage_key(&self) -> PeerStorageKey {
		self.peer_storage_key.clone()
	}

	fn get_receive_auth_key(&self) -> ReceiveAuthKey {
		self.receive_auth_key.clone()
	}

	fn sign_invoice(
		&self, invoice: &RawBolt11Invoice, recipient: Recipient,
	) -> Result<RecoverableSignature, ()> {
		let hash = invoice.signable_hash();
		let secret = match recipient {
			Recipient::Node => Ok(&self.node_secret),
			Recipient::PhantomNode => Err(()),
		}?;
		Ok(self.secp_ctx.sign_ecdsa_recoverable(&hash_to_message!(&hash), secret))
	}

	fn sign_bolt12_invoice(
		&self, invoice: &UnsignedBolt12Invoice,
	) -> Result<schnorr::Signature, ()> {
		let message = invoice.tagged_hash().as_digest();
		let keys = Keypair::from_secret_key(&self.secp_ctx, &self.node_secret);
		let aux_rand = self.get_secure_random_bytes();
		Ok(self.secp_ctx.sign_schnorr_with_aux_rand(message, &keys, &aux_rand))
	}

	fn sign_gossip_message(&self, msg: UnsignedGossipMessage) -> Result<Signature, ()> {
		let msg_hash = hash_to_message!(&Sha256dHash::hash(&msg.encode()[..])[..]);
		Ok(self.secp_ctx.sign_ecdsa(&msg_hash, &self.node_secret))
	}

	fn sign_message(&self, msg: &[u8]) -> Result<String, ()> {
		Ok(crate::util::message_signing::sign(msg, &self.node_secret))
	}
}

impl OutputSpender for KeysManager {
	/// Creates a [`Transaction`] which spends the given descriptors to the given outputs, plus an
	/// output to the given change destination (if sufficient change value remains).
	///
	/// See [`OutputSpender::spend_spendable_outputs`] documentation for more information.
	///
	/// We do not enforce that outputs meet the dust limit or that any output scripts are standard.
	///
	/// May panic if the [`SpendableOutputDescriptor`]s were not generated by channels which used
	/// this [`KeysManager`] or one of the [`InMemorySigner`] created by this [`KeysManager`].
	fn spend_spendable_outputs(
		&self, descriptors: &[&SpendableOutputDescriptor], outputs: Vec<TxOut>,
		change_destination_script: ScriptBuf, feerate_sat_per_1000_weight: u32,
		locktime: Option<LockTime>, secp_ctx: &Secp256k1<All>,
	) -> Result<Transaction, ()> {
		let (mut psbt, expected_max_weight) =
			SpendableOutputDescriptor::create_spendable_outputs_psbt(
				secp_ctx,
				descriptors,
				outputs,
				change_destination_script,
				feerate_sat_per_1000_weight,
				locktime,
			)?;
		psbt = self.sign_spendable_outputs_psbt(descriptors, psbt, secp_ctx)?;

		let spend_tx = psbt.extract_tx_unchecked_fee_rate();

		debug_assert!(expected_max_weight >= spend_tx.weight().to_wu());
		// Note that witnesses with a signature vary somewhat in size, so allow
		// `expected_max_weight` to overshoot by up to 3 bytes per input.
		debug_assert!(
			expected_max_weight <= spend_tx.weight().to_wu() + descriptors.len() as u64 * 3
		);

		Ok(spend_tx)
	}
}

impl SignerProvider for KeysManager {
	type EcdsaSigner = InMemorySigner;
	type TaprootSigner = InMemorySigner;

	fn generate_channel_keys_id(&self, _inbound: bool, user_channel_id: u128) -> [u8; 32] {
		let child_idx = self.channel_child_index.fetch_add(1, Ordering::AcqRel);
		// `child_idx` is the only thing guaranteed to make each channel unique without a restart
		// (though `user_channel_id` should help, depending on user behavior). If it manages to
		// roll over, we may generate duplicate keys for two different channels, which could result
		// in loss of funds. Because we only support 32-bit+ systems, assert that our `AtomicUsize`
		// doesn't reach `u32::MAX`.
		assert!(child_idx < core::u32::MAX as usize, "2^32 channels opened without restart");
		let mut id = [0; 32];
		id[0..4].copy_from_slice(&(child_idx as u32).to_be_bytes());
		id[4..8].copy_from_slice(&self.starting_time_nanos.to_be_bytes());
		id[8..16].copy_from_slice(&self.starting_time_secs.to_be_bytes());
		id[16..32].copy_from_slice(&user_channel_id.to_be_bytes());
		id
	}

	fn derive_channel_signer(&self, channel_keys_id: [u8; 32]) -> Self::EcdsaSigner {
		self.derive_channel_keys(&channel_keys_id)
	}

	fn derive_taproot_channel_signer(&self, channel_keys_id: [u8; 32]) -> Self::TaprootSigner {
		// EcdsaSigner == TaprootSigner == InMemorySigner here; the same key
		// material backs both signing schemes.
		self.derive_channel_keys(&channel_keys_id)
	}

	fn get_destination_script(&self, _channel_keys_id: [u8; 32]) -> Result<ScriptBuf, ()> {
		Ok(self.destination_script.clone())
	}

	fn get_shutdown_scriptpubkey(&self) -> Result<ShutdownScript, ()> {
		Ok(ShutdownScript::new_p2wpkh_from_pubkey(self.shutdown_pubkey.clone()))
	}
}

/// Similar to [`KeysManager`], but allows the node using this struct to receive phantom node
/// payments.
///
/// A phantom node payment is a payment made to a phantom invoice, which is an invoice that can be
/// paid to one of multiple nodes. This works because we encode the invoice route hints such that
/// LDK will recognize an incoming payment as destined for a phantom node, and collect the payment
/// itself without ever needing to forward to this fake node.
///
/// Phantom node payments are useful for load balancing between multiple LDK nodes. They also
/// provide some fault tolerance, because payers will automatically retry paying other provided
/// nodes in the case that one node goes down.
///
/// Note that multi-path payments are not supported in phantom invoices for security reasons.
// In the hypothetical case that we did support MPP phantom payments, there would be no way for
// nodes to know when the full payment has been received (and the preimage can be released) without
// significantly compromising on our safety guarantees. I.e., if we expose the ability for the user
// to tell LDK when the preimage can be released, we open ourselves to attacks where the preimage
// is released too early.
//
/// Switching between this struct and [`KeysManager`] will invalidate any previously issued
/// invoices and attempts to pay previous invoices will fail.
pub struct PhantomKeysManager {
	#[cfg(test)]
	pub(crate) inner: KeysManager,
	#[cfg(not(test))]
	inner: KeysManager,
	inbound_payment_key: ExpandedKey,
	phantom_secret: SecretKey,
	phantom_node_id: PublicKey,
}

impl EntropySource for PhantomKeysManager {
	fn get_secure_random_bytes(&self) -> [u8; 32] {
		self.inner.get_secure_random_bytes()
	}
}

impl NodeSigner for PhantomKeysManager {
	fn get_node_id(&self, recipient: Recipient) -> Result<PublicKey, ()> {
		match recipient {
			Recipient::Node => self.inner.get_node_id(Recipient::Node),
			Recipient::PhantomNode => Ok(self.phantom_node_id.clone()),
		}
	}

	fn ecdh(
		&self, recipient: Recipient, other_key: &PublicKey, tweak: Option<&Scalar>,
	) -> Result<SharedSecret, ()> {
		let mut node_secret = match recipient {
			Recipient::Node => self.inner.node_secret.clone(),
			Recipient::PhantomNode => self.phantom_secret.clone(),
		};
		if let Some(tweak) = tweak {
			node_secret = node_secret.mul_tweak(tweak).map_err(|_| ())?;
		}
		Ok(SharedSecret::new(other_key, &node_secret))
	}

	fn get_expanded_key(&self) -> ExpandedKey {
		self.inbound_payment_key.clone()
	}

	fn get_peer_storage_key(&self) -> PeerStorageKey {
		self.inner.peer_storage_key.clone()
	}

	fn get_receive_auth_key(&self) -> ReceiveAuthKey {
		self.inner.receive_auth_key.clone()
	}

	fn sign_invoice(
		&self, invoice: &RawBolt11Invoice, recipient: Recipient,
	) -> Result<RecoverableSignature, ()> {
		let hash = invoice.signable_hash();
		let secret = match recipient {
			Recipient::Node => &self.inner.node_secret,
			Recipient::PhantomNode => &self.phantom_secret,
		};
		Ok(self.inner.secp_ctx.sign_ecdsa_recoverable(&hash_to_message!(&hash), secret))
	}

	fn sign_bolt12_invoice(
		&self, invoice: &UnsignedBolt12Invoice,
	) -> Result<schnorr::Signature, ()> {
		self.inner.sign_bolt12_invoice(invoice)
	}

	fn sign_gossip_message(&self, msg: UnsignedGossipMessage) -> Result<Signature, ()> {
		self.inner.sign_gossip_message(msg)
	}

	fn sign_message(&self, msg: &[u8]) -> Result<String, ()> {
		self.inner.sign_message(msg)
	}
}

impl OutputSpender for PhantomKeysManager {
	/// See [`OutputSpender::spend_spendable_outputs`] and [`KeysManager::spend_spendable_outputs`]
	/// for documentation on this method.
	fn spend_spendable_outputs(
		&self, descriptors: &[&SpendableOutputDescriptor], outputs: Vec<TxOut>,
		change_destination_script: ScriptBuf, feerate_sat_per_1000_weight: u32,
		locktime: Option<LockTime>, secp_ctx: &Secp256k1<All>,
	) -> Result<Transaction, ()> {
		self.inner.spend_spendable_outputs(
			descriptors,
			outputs,
			change_destination_script,
			feerate_sat_per_1000_weight,
			locktime,
			secp_ctx,
		)
	}
}

impl SignerProvider for PhantomKeysManager {
	type EcdsaSigner = InMemorySigner;
	type TaprootSigner = InMemorySigner;

	fn generate_channel_keys_id(&self, inbound: bool, user_channel_id: u128) -> [u8; 32] {
		self.inner.generate_channel_keys_id(inbound, user_channel_id)
	}

	fn derive_channel_signer(&self, channel_keys_id: [u8; 32]) -> Self::EcdsaSigner {
		self.inner.derive_channel_signer(channel_keys_id)
	}

	fn derive_taproot_channel_signer(&self, channel_keys_id: [u8; 32]) -> Self::TaprootSigner {
		self.inner.derive_taproot_channel_signer(channel_keys_id)
	}

	fn get_destination_script(&self, channel_keys_id: [u8; 32]) -> Result<ScriptBuf, ()> {
		self.inner.get_destination_script(channel_keys_id)
	}

	fn get_shutdown_scriptpubkey(&self) -> Result<ShutdownScript, ()> {
		self.inner.get_shutdown_scriptpubkey()
	}
}

impl PhantomKeysManager {
	/// Constructs a [`PhantomKeysManager`] given a 32-byte seed and an additional `cross_node_seed`
	/// that is shared across all nodes that intend to participate in [phantom node payments]
	/// together.
	///
	/// See [`KeysManager::new`] for more information on `seed`, `starting_time_secs`,
	/// `starting_time_nanos`, and `v2_remote_key_derivation`.
	///
	/// `cross_node_seed` must be the same across all phantom payment-receiving nodes and also the
	/// same across restarts, or else inbound payments may fail.
	///
	/// [phantom node payments]: PhantomKeysManager
	pub fn new(
		seed: &[u8; 32], starting_time_secs: u64, starting_time_nanos: u32,
		cross_node_seed: &[u8; 32], v2_remote_key_derivation: bool,
	) -> Self {
		let inner = KeysManager::new(
			seed,
			starting_time_secs,
			starting_time_nanos,
			v2_remote_key_derivation,
		);
		let (inbound_key, phantom_key) = hkdf_extract_expand_twice(
			b"LDK Inbound and Phantom Payment Key Expansion",
			cross_node_seed,
		);
		let phantom_secret = SecretKey::from_slice(&phantom_key).unwrap();
		let phantom_node_id = PublicKey::from_secret_key(&inner.secp_ctx, &phantom_secret);
		Self {
			inner,
			inbound_payment_key: ExpandedKey::new(inbound_key),
			phantom_secret,
			phantom_node_id,
		}
	}

	/// See [`KeysManager::derive_channel_keys`] for documentation on this method.
	pub fn derive_channel_keys(&self, params: &[u8; 32]) -> InMemorySigner {
		self.inner.derive_channel_keys(params)
	}

	/// Gets the "node_id" secret key used to sign gossip announcements, decode onion data, etc.
	pub fn get_node_secret_key(&self) -> SecretKey {
		self.inner.get_node_secret_key()
	}

	/// Gets the "node_id" secret key of the phantom node used to sign invoices, decode the
	/// last-hop onion data, etc.
	pub fn get_phantom_node_secret_key(&self) -> SecretKey {
		self.phantom_secret
	}
}

/// An implementation of [`EntropySource`] using ChaCha20.
pub struct RandomBytes {
	/// Seed from which all randomness produced is derived from.
	seed: [u8; 32],
	/// Tracks the number of times we've produced randomness to ensure we don't return the same
	/// bytes twice.
	index: AtomicCounter,
}

impl RandomBytes {
	/// Creates a new instance using the given seed.
	pub fn new(seed: [u8; 32]) -> Self {
		Self { seed, index: AtomicCounter::new() }
	}
}

impl EntropySource for RandomBytes {
	fn get_secure_random_bytes(&self) -> [u8; 32] {
		let index = self.index.next();
		let mut nonce = [0u8; 16];
		nonce[..8].copy_from_slice(&index.to_be_bytes());
		ChaCha20::get_single_block(&self.seed, &nonce)
	}
}

// Ensure that EcdsaChannelSigner can have a vtable
#[test]
pub fn dyn_sign() {
	let _signer: Box<dyn EcdsaChannelSigner>;
}

// §10 audit area 3/11 (coop-close RBF nonce + no nonce reuse): the per-round closing
// nonce height MUST be distinct for every distinct close round (so two distinct close
// txs never share a MuSig2 nonce → no funding-key leak, spec §9f-0), AND the closing /
// splice nonce-height domains must be disjoint from the commitment-height range
// ([0, 2^48)) and from each other, so a closing-round nonce can never collide with a
// commitment or splice nonce on the same shachain root.
#[test]
fn taproot_closing_and_splice_nonce_heights_disjoint_and_distinct() {
	use bitcoin::hashes::Hash;
	use bitcoin::Txid;

	// Per-round closing heights are strictly decreasing from the sentinel and unique.
	let h0 = closing_nonce_height(0);
	let h1 = closing_nonce_height(1);
	let h2 = closing_nonce_height(2);
	assert_eq!(h0, CLOSING_NONCE_BASE);
	assert!(h0 > h1 && h1 > h2, "each closing round gets a strictly distinct height");

	// Closing heights live at the very top (near u64::MAX), strictly ABOVE the
	// commitment range [0, 2^48) and the splice window [2^48, 2^56 + 2^48).
	const COMMITMENT_TOP: u64 = 1u64 << 48;
	const SPLICE_TOP: u64 = (1u64 << 56) + (1u64 << 48);
	for r in 0..1000u64 {
		let h = closing_nonce_height(r);
		assert!(h >= SPLICE_TOP, "closing nonce height must be above the splice window");
	}

	// Distinct splice txids → distinct splice nonce heights, all inside the disjoint
	// [2^48, 2^56 + 2^48) window (above commitments, below the closing range).
	let txid_a = Txid::from_slice(&[0x11; 32]).unwrap();
	let txid_b = Txid::from_slice(&[0x22; 32]).unwrap();
	let sa = splice_nonce_height(&txid_a);
	let sb = splice_nonce_height(&txid_b);
	assert_ne!(sa, sb, "distinct splices get distinct nonce heights (§9f-0 reuse guard)");
	for s in [sa, sb] {
		assert!(s >= COMMITMENT_TOP, "splice nonce height is above the commitment range");
		assert!(s < SPLICE_TOP, "splice nonce height is below the closing range");
	}
}

#[cfg(ldk_bench)]
pub mod benches {
	use crate::sign::{EntropySource, KeysManager};
	use bitcoin::constants::genesis_block;
	use bitcoin::Network;
	use std::sync::mpsc::TryRecvError;
	use std::sync::{mpsc, Arc};
	use std::thread;
	use std::time::Duration;

	use criterion::Criterion;

	pub fn bench_get_secure_random_bytes(bench: &mut Criterion) {
		let seed = [0u8; 32];
		let now = Duration::from_secs(genesis_block(Network::Testnet).header.time as u64);
		let keys_manager =
			Arc::new(KeysManager::new(&seed, now.as_secs(), now.subsec_micros(), true));

		let mut handles = Vec::new();
		let mut stops = Vec::new();
		for _ in 1..5 {
			let keys_manager_clone = Arc::clone(&keys_manager);
			let (stop_sender, stop_receiver) = mpsc::channel();
			let handle = thread::spawn(move || loop {
				keys_manager_clone.get_secure_random_bytes();
				match stop_receiver.try_recv() {
					Ok(_) | Err(TryRecvError::Disconnected) => {
						println!("Terminating.");
						break;
					},
					Err(TryRecvError::Empty) => {},
				}
			});
			handles.push(handle);
			stops.push(stop_sender);
		}

		bench.bench_function("get_secure_random_bytes", |b| {
			b.iter(|| keys_manager.get_secure_random_bytes())
		});

		for stop in stops {
			let _ = stop.send(());
		}
		for handle in handles {
			handle.join().unwrap();
		}
	}
}
