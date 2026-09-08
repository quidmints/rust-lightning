//! MuSig2 (BIP327) key-path signing core for **simple taproot channels**, in-tree.
//!
//! This is the *exact* proven signing core from `quid_ln::taproot_signer`
//! (`docs/TAPROOT-CHANNELS-BUILD-SPEC.md` §1), ported into the `lightning` crate
//! so [`crate::sign::InMemorySigner`]'s `TaprootChannelSigner` bodies can produce
//! key-path MuSig2 partials/aggregates **without** depending on `quid-ln` (which
//! depends on `lightning`, so the reverse edge is impossible). The two copies are
//! byte-for-byte equivalent — same KeySort+KeyAgg+`with_unspendable_taproot_tweak`
//! `Q`, same deterministic per-height shachain nonce — so an `InMemorySigner` and
//! a `ValidatingChannelSigner` interop on the same channel.
//!
//! ## Nonce scheme (BIP327 §nonce-gen + BOLT, spec §1)
//!
//! ```text
//!   musig2_shachain_root = sha256(shachain_root)            // domain-separate
//!   nonce_seed(height)   = HMAC-SHA256(key = musig2_shachain_root,
//!                                      msg = height.to_be_bytes())
//! ```
//!
//! Deterministic per **commitment height**, re-derivable (crash-safe), never
//! random, never persisted — superseding any "randomize the nonce" instruction.

use bitcoin::hashes::{sha256, Hash, HashEngine, Hmac, HmacEngine};

use musig2::secp256k1::{schnorr, PublicKey, SecretKey, XOnlyPublicKey};
use musig2::{
	aggregate_partial_signatures, AggNonce, FirstRound, KeyAggContext, PartialSignature, PubNonce,
	SecNonceSpices, SecondRound,
};

/// Domain-separation: `sha256(shachain_root)` is the HMAC key (spec §1).
fn musig2_shachain_root(shachain_root: &[u8; 32]) -> sha256::Hash {
	sha256::Hash::hash(shachain_root)
}

/// Deterministic 32-byte MuSig2 secret-nonce *seed* for `height`:
/// `HMAC-SHA256(key = sha256(shachain_root), msg = height_be)`.
pub fn derive_secnonce_seed(shachain_root: &[u8; 32], height: u64) -> [u8; 32] {
	let key = musig2_shachain_root(shachain_root);
	let mut engine = HmacEngine::<sha256::Hash>::new(&key[..]);
	engine.input(&height.to_be_bytes());
	let mac: Hmac<sha256::Hash> = Hmac::from_engine(engine);
	*mac.as_byte_array()
}

/// Domain separator mixed into the secret-nonce seed for the **counterparty's**
/// commitment. Holder and counterparty commitments are signed at the SAME
/// commitment height (both count down from `INITIAL_COMMITMENT_NUMBER` in
/// lockstep), so an untagged `(root, height)` seed yields the SAME nonce for
/// both — and signing the two different commitment sighashes under one nonce
/// leaks the funding key (`x = (s1 - s2)/(e1 - e2)`). The holder path keeps the
/// untagged seed; only the counterparty path is tagged, so the two nonces are
/// unconditionally distinct at every height.
pub const COUNTERPARTY_COMMITMENT_NONCE_TAG: &[u8] = b"quid/musig2/counterparty-commitment";

/// Domain-separated [`derive_secnonce_seed`]: HMACs `domain || height` so a
/// tagged derivation can never collide with the untagged holder-commitment seed
/// at the same height (height-uniqueness is preserved within a domain).
pub fn derive_secnonce_seed_domain(
	shachain_root: &[u8; 32], height: u64, domain: &[u8],
) -> [u8; 32] {
	let key = musig2_shachain_root(shachain_root);
	let mut engine = HmacEngine::<sha256::Hash>::new(&key[..]);
	engine.input(domain);
	engine.input(&height.to_be_bytes());
	let mac: Hmac<sha256::Hash> = Hmac::from_engine(engine);
	*mac.as_byte_array()
}

/// Errors building the per-channel [`KeyAggContext`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KeyAggError {
	/// A funding key was not a valid 33-byte compressed secp256k1 point.
	BadPubkey,
	/// The two keys aggregated to the point at infinity (degenerate input).
	Aggregate,
	/// The taproot tweak produced the point at infinity (degenerate input).
	Tweak,
	/// `my_funding_pubkey` is neither of the two channel participants.
	NotAParticipant,
}

/// KeySort the two 33-byte compressed funding keys lexicographically, build the
/// cached [`KeyAggContext`] with the BIP341 §158 key-path-only (empty merkle
/// root) taproot tweak, and report our slot in the sorted list. Identical to
/// `quid_ln::taproot_signer::channel_key_agg_ctx` and
/// [`crate::ln::chan_utils::taproot_funding_aggregate_xonly`].
pub fn channel_key_agg_ctx(
	lp: &[u8; 33], hop: &[u8; 33], my_funding_pubkey: &[u8; 33],
) -> Result<(KeyAggContext, usize), KeyAggError> {
	let (lo, hi) = if lp[..] < hop[..] { (lp, hop) } else { (hop, lp) };
	let lo_pk = PublicKey::from_slice(lo).map_err(|_| KeyAggError::BadPubkey)?;
	let hi_pk = PublicKey::from_slice(hi).map_err(|_| KeyAggError::BadPubkey)?;

	let ctx = KeyAggContext::new([lo_pk, hi_pk])
		.map_err(|_| KeyAggError::Aggregate)?
		.with_unspendable_taproot_tweak()
		.map_err(|_| KeyAggError::Tweak)?;

	let signer_index = if my_funding_pubkey[..] == lo[..] {
		0
	} else if my_funding_pubkey[..] == hi[..] {
		1
	} else {
		return Err(KeyAggError::NotAParticipant);
	};
	Ok((ctx, signer_index))
}

/// The x-only tweaked aggregate output key `Q` (the BIP340 verification key and
/// the key committed in `0x5120 || Q`).
pub fn aggregated_xonly(ctx: &KeyAggContext) -> XOnlyPublicKey {
	let q: PublicKey = ctx.aggregated_pubkey();
	q.x_only_public_key().0
}

/// Errors in the key-path signing flow.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SignError {
	/// Failed to set up the first round (bad signer index / key mismatch).
	RoundSetup,
	/// Failed to place the counterparty's public nonce.
	Nonce,
	/// Failed to finalize the first round (partial sign).
	Finalize,
	/// The counterparty's partial signature failed verification.
	PartialVerify,
	/// Final aggregation failed.
	Aggregate,
}

/// Derive **our** deterministic public nonce for `height` through the same
/// conduition `FirstRound` derivation the signing path uses (binds the aggregated
/// pubkey + signer index + spices into the secret nonce). MUST be used to
/// advertise the nonce we later sign with; any other derivation yields a
/// different nonce and aggregation fails.
pub fn local_pubnonce(
	ctx: KeyAggContext, our_index: usize, shachain_root: &[u8; 32], height: u64,
) -> Result<PubNonce, SignError> {
	let seed = derive_secnonce_seed(shachain_root, height);
	let round =
		FirstRound::new(ctx, seed, our_index, SecNonceSpices::new()).map_err(|_| SignError::RoundSetup)?;
	Ok(round.our_public_nonce())
}

/// Produce **our** key-path partial over `message`, given the counterparty's
/// public nonce. Returns our partial + our pubnonce (the `partial_signature_with_
/// nonce` payload). The single-party half of the 2-party round (spec §1).
#[allow(clippy::too_many_arguments)]
pub fn our_key_path_partial(
	ctx: KeyAggContext, our_index: usize, counterparty_index: usize, seckey: SecretKey,
	shachain_root: &[u8; 32], height: u64, counterparty_nonce: PubNonce, message: [u8; 32],
) -> Result<(PartialSignature, PubNonce), SignError> {
	let seed = derive_secnonce_seed(shachain_root, height);
	let mut r1 =
		FirstRound::new(ctx, seed, our_index, SecNonceSpices::new()).map_err(|_| SignError::RoundSetup)?;
	let our_pubnonce = r1.our_public_nonce();
	r1.receive_nonce(counterparty_index, counterparty_nonce).map_err(|_| SignError::Nonce)?;
	let r2: SecondRound<[u8; 32]> =
		r1.finalize(seckey, message).map_err(|_| SignError::Finalize)?;
	Ok((r2.our_signature(), our_pubnonce))
}

/// Counterparty-commitment variant of [`our_key_path_partial`]: identical except
/// the secret nonce is derived from a DOMAIN-SEPARATED seed
/// ([`COUNTERPARTY_COMMITMENT_NONCE_TAG`]) so it can never equal the
/// holder-commitment nonce at the same height (the funding-key-leak guard). The
/// returned pubnonce is what we advertise alongside the partial
/// (`partial_signature_with_nonce`); the peer verifies/aggregates against THAT
/// nonce, so the holder advertisement (`next_local_nonce`) and
/// `finalize_holder_commitment` (both untagged) stay matched and unchanged.
#[allow(clippy::too_many_arguments)]
pub fn our_key_path_partial_counterparty(
	ctx: KeyAggContext, our_index: usize, counterparty_index: usize, seckey: SecretKey,
	shachain_root: &[u8; 32], height: u64, counterparty_nonce: PubNonce, message: [u8; 32],
) -> Result<(PartialSignature, PubNonce), SignError> {
	let seed = derive_secnonce_seed_domain(shachain_root, height, COUNTERPARTY_COMMITMENT_NONCE_TAG);
	// NONCE-REUSE / FUNDING-KEY-LEAK GUARD: bind the secret nonce to the counterparty's
	// public nonce AND the message (BIP327 `SecNonceSpices`). A malicious peer can rotate
	// its nonce on `channel_reestablish` and induce us to re-sign the SAME (root, height)
	// counterparty commitment (we retransmit `commitment_signed`). With a secret nonce fixed
	// only by (root, height) that reuses it across two DIFFERENT challenges — leaking the
	// funding key via `x = (s1 - s2)/(e1 - e2)`. Binding re-randomises the secret nonce for
	// any rotated nonce/message, so no two distinct signing sessions ever share one. It stays
	// interop-safe (our pubnonce is sent WITH the partial in `partial_signature_with_nonce`,
	// never pre-advertised) and crash-safe (deterministic in the fixed inputs).
	let cp_nonce_bytes = counterparty_nonce.serialize();
	let spices = SecNonceSpices::new().with_message(&message).with_extra_input(&cp_nonce_bytes);
	let mut r1 =
		FirstRound::new(ctx, seed, our_index, spices).map_err(|_| SignError::RoundSetup)?;
	let our_pubnonce = r1.our_public_nonce();
	r1.receive_nonce(counterparty_index, counterparty_nonce).map_err(|_| SignError::Nonce)?;
	let r2: SecondRound<[u8; 32]> =
		r1.finalize(seckey, message).map_err(|_| SignError::Finalize)?;
	Ok((r2.our_signature(), our_pubnonce))
}

/// Aggregate **our** + the **counterparty's** key-path partials (each with their
/// pubnonce) into the final BIP340 key-path [`schnorr::Signature`] that spends the
/// `0x5120||Q` funding output. conduition verifies each partial on aggregate and
/// errors on a bad one (spec §1). The two nonces are summed (commutative); the
/// partials MUST be placed by signer index.
#[allow(clippy::too_many_arguments)]
pub fn aggregate_key_path_partials(
	ctx: KeyAggContext, message: [u8; 32], our_index: usize, our_pubnonce: PubNonce,
	our_partial: PartialSignature, counterparty_index: usize, counterparty_pubnonce: PubNonce,
	counterparty_partial: PartialSignature,
) -> Result<schnorr::Signature, SignError> {
	let agg_nonce = AggNonce::sum([&our_pubnonce, &counterparty_pubnonce]);
	let mut partials: [PartialSignature; 2] = [musig2::secp::MaybeScalar::Zero; 2];
	partials[our_index] = our_partial;
	partials[counterparty_index] = counterparty_partial;
	aggregate_partial_signatures(&ctx, &agg_nonce, partials, message)
		.map_err(|_| SignError::Aggregate)
}

#[cfg(test)]
mod tests {
	use super::*;
	use musig2::secp256k1::{Message, Secp256k1};

	fn keypair(seed: u8) -> (SecretKey, [u8; 33]) {
		let secp = Secp256k1::new();
		let sk = SecretKey::from_slice(&[seed; 32]).unwrap();
		(sk, sk.public_key(&secp).serialize())
	}

	/// The in-tree core reproduces the proven roundtrip: deterministic nonces,
	/// per-signer partials, aggregate verifies vs the tweaked `Q` under BIP340.
	#[test]
	fn in_tree_key_path_roundtrip_verifies() {
		let secp = Secp256k1::new();
		let (lp_sec, lp_pub) = keypair(0x11);
		let (hop_sec, hop_pub) = keypair(0x22);
		let lp_root = [0xAB; 32];
		let hop_root = [0xCD; 32];
		let height = 281_474_976_710_654u64;
		let msg = [0x42u8; 32];

		let (lp_ctx, lp_idx) = channel_key_agg_ctx(&lp_pub, &hop_pub, &lp_pub).unwrap();
		let (hop_ctx, hop_idx) = channel_key_agg_ctx(&lp_pub, &hop_pub, &hop_pub).unwrap();
		let q = aggregated_xonly(&lp_ctx);

		let lp_pn = local_pubnonce(lp_ctx, lp_idx, &lp_root, height).unwrap();
		let hop_pn = local_pubnonce(hop_ctx, hop_idx, &hop_root, height).unwrap();

		let (lp_ctx2, _) = channel_key_agg_ctx(&lp_pub, &hop_pub, &lp_pub).unwrap();
		let (hop_ctx2, _) = channel_key_agg_ctx(&lp_pub, &hop_pub, &hop_pub).unwrap();
		let (lp_partial, lp_pn2) = our_key_path_partial(
			lp_ctx2, lp_idx, hop_idx, lp_sec, &lp_root, height, hop_pn.clone(), msg,
		)
		.unwrap();
		let (hop_partial, _hop_pn2) = our_key_path_partial(
			hop_ctx2, hop_idx, lp_idx, hop_sec, &hop_root, height, lp_pn.clone(), msg,
		)
		.unwrap();
		assert_eq!(lp_pn.serialize(), lp_pn2.serialize());

		let (agg_ctx, _) = channel_key_agg_ctx(&lp_pub, &hop_pub, &lp_pub).unwrap();
		let sig = aggregate_key_path_partials(
			agg_ctx, msg, lp_idx, lp_pn, lp_partial, hop_idx, hop_pn, hop_partial,
		)
		.unwrap();
		secp.verify_schnorr(&sig, &Message::from_digest(msg), &q)
			.expect("in-tree aggregated key-path sig verifies vs Q");
	}

	/// §10 cluster-D #1 (the catastrophic SILENT splice case). A splice rotates each
	/// party's INDIVIDUAL funding key by `SHA256(prev_funding_txid || sk)` (BOLT #995),
	/// then both sides re-`KeyAgg` into `Q'`. `our_index`/`cp_index` come from the
	/// LEXICOGRAPHIC KeySort of the 33-byte compressed keys. If the ROTATED pair sorts
	/// in the OPPOSITE order from the ORIGINAL pair, a signer that CACHED the original
	/// index would now sign/aggregate at the WRONG slot → bad partial / swapped roles.
	///
	/// This test CONSTRUCTS exactly that adversarial case: it searches `prev_funding_txid`
	/// candidates until the rotation FLIPS the (lp,hop) sort order, then drives the full
	/// post-splice MuSig2 roundtrip (nonce + partial + aggregate) over `Q'` and asserts
	/// the BIP340 sig verifies. The index is re-derived from the ROTATED keys at every
	/// site (`channel_key_agg_ctx`), so the flip is handled correctly — this confirms
	/// the no-cached-index invariant rather than relying on a happy-path that keeps order.
	#[test]
	fn order_flipping_splice_rotation_aggregate_verifies() {
		use crate::sign::compute_funding_key_tweak;
		use bitcoin::hashes::Hash as _;
		use bitcoin::Txid;

		let secp = Secp256k1::new();

		// Base (pre-splice) individual funding secret keys for lp and hop.
		let lp_base = SecretKey::from_slice(&[0x11; 32]).unwrap();
		let hop_base = SecretKey::from_slice(&[0x22; 32]).unwrap();
		let lp_base_pub = lp_base.public_key(&secp).serialize();
		let hop_base_pub = hop_base.public_key(&secp).serialize();
		// Original sort order: which of lp/hop is `lo`.
		let orig_lp_is_lo = lp_base_pub[..] < hop_base_pub[..];

		// Rotate by `SHA256(txid || sk)` exactly as `InMemorySigner::funding_key(Some(txid))`.
		let rotate = |base: &SecretKey, txid: &Txid| -> SecretKey {
			let tweak = compute_funding_key_tweak(base, txid);
			base.add_tweak(&tweak).expect("non-degenerate tweak")
		};

		// Search prev_funding_txid candidates until the ROTATED pair FLIPS the sort.
		let mut found: Option<(Txid, SecretKey, SecretKey, [u8; 33], [u8; 33])> = None;
		for n in 0u32..10_000 {
			let mut raw = [0u8; 32];
			raw[..4].copy_from_slice(&n.to_be_bytes());
			let txid = Txid::from_slice(&raw).unwrap();
			let lp_rot = rotate(&lp_base, &txid);
			let hop_rot = rotate(&hop_base, &txid);
			let lp_rot_pub = lp_rot.public_key(&secp).serialize();
			let hop_rot_pub = hop_rot.public_key(&secp).serialize();
			let rot_lp_is_lo = lp_rot_pub[..] < hop_rot_pub[..];
			if rot_lp_is_lo != orig_lp_is_lo {
				found = Some((txid, lp_rot, hop_rot, lp_rot_pub, hop_rot_pub));
				break;
			}
		}
		let (_txid, lp_rot, hop_rot, lp_rot_pub, hop_rot_pub) =
			found.expect("must find a prev_funding_txid that flips the sort order");

		// Sanity: the rotated pair really does sort the OTHER way than the base pair.
		assert_ne!(
			lp_rot_pub[..] < hop_rot_pub[..],
			orig_lp_is_lo,
			"constructed case must flip the KeySort order across the splice"
		);

		// Post-splice roundtrip over Q': each party derives its index from the ROTATED
		// keys (as taproot_key_agg / verify_taproot_keyspend_partials do in production).
		let lp_root = [0xA1; 32];
		let hop_root = [0xB2; 32];
		let height = 7u64;
		let msg = [0x5Cu8; 32];

		let (lp_ctx, lp_idx) =
			channel_key_agg_ctx(&lp_rot_pub, &hop_rot_pub, &lp_rot_pub).unwrap();
		let (hop_ctx, hop_idx) =
			channel_key_agg_ctx(&lp_rot_pub, &hop_rot_pub, &hop_rot_pub).unwrap();
		// The two parties land at distinct, complementary slots.
		assert_ne!(lp_idx, hop_idx);
		assert_eq!(lp_idx, 1 - hop_idx);
		let q = aggregated_xonly(&lp_ctx);

		let lp_pn = local_pubnonce(lp_ctx, lp_idx, &lp_root, height).unwrap();
		let hop_pn = local_pubnonce(hop_ctx, hop_idx, &hop_root, height).unwrap();

		let (lp_ctx2, _) = channel_key_agg_ctx(&lp_rot_pub, &hop_rot_pub, &lp_rot_pub).unwrap();
		let (hop_ctx2, _) = channel_key_agg_ctx(&lp_rot_pub, &hop_rot_pub, &hop_rot_pub).unwrap();
		let (lp_partial, lp_pn2) = our_key_path_partial(
			lp_ctx2, lp_idx, hop_idx, lp_rot, &lp_root, height, hop_pn.clone(), msg,
		)
		.unwrap();
		let (hop_partial, _) = our_key_path_partial(
			hop_ctx2, hop_idx, lp_idx, hop_rot, &hop_root, height, lp_pn.clone(), msg,
		)
		.unwrap();
		assert_eq!(lp_pn.serialize(), lp_pn2.serialize());

		let (agg_ctx, _) = channel_key_agg_ctx(&lp_rot_pub, &hop_rot_pub, &lp_rot_pub).unwrap();
		let sig = aggregate_key_path_partials(
			agg_ctx, msg, lp_idx, lp_pn, lp_partial, hop_idx, hop_pn, hop_partial,
		)
		.expect("post-flip splice partials aggregate");
		secp.verify_schnorr(&sig, &Message::from_digest(msg), &q)
			.expect("post-flip-splice aggregated key-path sig verifies vs Q'");
	}

	#[test]
	fn nonce_seed_is_deterministic_per_height() {
		let root = [0x07; 32];
		assert_eq!(derive_secnonce_seed(&root, 100), derive_secnonce_seed(&root, 100));
		assert_ne!(derive_secnonce_seed(&root, 100), derive_secnonce_seed(&root, 101));
	}

	/// FUNDING-KEY-LEAK GUARD: the holder and counterparty commitments are signed
	/// at the SAME commitment height (both numbers count down from
	/// `INITIAL_COMMITMENT_NUMBER` in lockstep), so `our_key_path_partial` (holder
	/// finalize, untagged) and `our_key_path_partial_counterparty` (tagged) MUST
	/// derive DISTINCT nonces — else signing the two different commitment sighashes
	/// under one nonce leaks the funding key (`x = (s1 - s2)/(e1 - e2)`).
	#[test]
	fn counterparty_nonce_domain_separated_from_holder_at_same_height() {
		let (_lp_sec, lp_pub) = keypair(0x11);
		let (_hop_sec, hop_pub) = keypair(0x22);
		let root = [0x5A; 32];
		let height = (1u64 << 48) - 1; // INITIAL_COMMITMENT_NUMBER (holder# == counterparty#)

		assert_ne!(
			derive_secnonce_seed(&root, height),
			derive_secnonce_seed_domain(&root, height, COUNTERPARTY_COMMITMENT_NONCE_TAG),
			"counterparty-tagged seed must differ from the untagged holder seed at the same height",
		);

		let (ctx_h, idx) = channel_key_agg_ctx(&lp_pub, &hop_pub, &lp_pub).unwrap();
		let (ctx_c, _) = channel_key_agg_ctx(&lp_pub, &hop_pub, &lp_pub).unwrap();
		let holder_pn = local_pubnonce(ctx_h, idx, &root, height).unwrap();
		let cp_seed = derive_secnonce_seed_domain(&root, height, COUNTERPARTY_COMMITMENT_NONCE_TAG);
		let cp_pn = FirstRound::new(ctx_c, cp_seed, idx, SecNonceSpices::new())
			.unwrap()
			.our_public_nonce();
		assert_ne!(
			holder_pn.serialize(),
			cp_pn.serialize(),
			"holder and counterparty commitment nonces MUST differ at the same height (funding-key-leak guard)",
		);
	}

	/// FUNDING-KEY-LEAK GUARD (nonce-reuse): the counterparty-commitment secret nonce is
	/// bound to the counterparty's public nonce AND the message (via `SecNonceSpices`), so
	/// re-signing the SAME `(root, height)` against a ROTATED counterparty nonce — reachable
	/// when a peer sends a fresh `next_local_nonce` on `channel_reestablish` and we
	/// retransmit `commitment_signed` — derives a DIFFERENT secret nonce (distinct public
	/// nonce). Without this, three re-signs over one reused secret nonce solve the BIP327
	/// two-nonce system for our funding key. Interop is preserved: our pubnonce is sent WITH
	/// the partial (`partial_signature_with_nonce`), never pre-advertised.
	#[test]
	fn counterparty_commitment_nonce_binds_to_peer_nonce_and_message() {
		let (lp_sec, lp_pub) = keypair(0x11);
		let (hop_sec, hop_pub) = keypair(0x22);
		let root = [0x5A; 32];
		let height = 1_000u64;
		let msg = [0x9Au8; 32];

		let (_c, lp_idx) = channel_key_agg_ctx(&lp_pub, &hop_pub, &lp_pub).unwrap();
		let (_c2, hop_idx) = channel_key_agg_ctx(&lp_pub, &hop_pub, &hop_pub).unwrap();

		let cp = |seed: [u8; 32]| -> PubNonce {
			let (ctx, _) = channel_key_agg_ctx(&lp_pub, &hop_pub, &hop_pub).unwrap();
			local_pubnonce(ctx, hop_idx, &seed, height).unwrap()
		};
		let sign_cp = |cpn: &PubNonce, m: [u8; 32]| {
			let (ctx, _) = channel_key_agg_ctx(&lp_pub, &hop_pub, &lp_pub).unwrap();
			our_key_path_partial_counterparty(
				ctx, lp_idx, hop_idx, lp_sec, &root, height, cpn.clone(), m,
			)
			.unwrap()
		};

		// SAME (root, height) — a ROTATED counterparty nonce yields a DIFFERENT secret nonce
		// (⇒ different public nonce). This is the property that defeats the reuse extraction.
		let (cp1, cp2) = (cp([0xB1; 32]), cp([0xB2; 32]));
		let (_s1, pn1) = sign_cp(&cp1, msg);
		let (_s2, pn2) = sign_cp(&cp2, msg);
		assert_ne!(
			pn1.serialize(), pn2.serialize(),
			"rotated counterparty nonce MUST rotate our secret nonce (no reuse)"
		);
		// A different message at the same height also rotates the secret nonce.
		let (_s3, pn3) = sign_cp(&cp1, [0x77u8; 32]);
		assert_ne!(pn1.serialize(), pn3.serialize(), "different message MUST rotate our secret nonce");

		// Determinism/crash-safety preserved: identical (root, height, cp_nonce, message)
		// re-derives the identical nonce + partial (re-signable after reload).
		let (s1a, pn1a) = sign_cp(&cp1, msg);
		let (s1b, pn1b) = sign_cp(&cp1, msg);
		assert_eq!(pn1a.serialize(), pn1b.serialize(), "same inputs ⇒ same nonce (crash-safe)");
		assert_eq!(s1a, s1b, "same inputs ⇒ same partial (crash-safe)");

		// Interop preserved: the partial still aggregates with the peer's to a BIP340 sig
		// verifying vs Q, using the pubnonce we send alongside the partial.
		let secp = Secp256k1::new();
		let (agg_ctx, _) = channel_key_agg_ctx(&lp_pub, &hop_pub, &lp_pub).unwrap();
		let q = aggregated_xonly(&agg_ctx);
		let (our_partial, our_pn) = sign_cp(&cp1, msg);
		// The hop signs against our (bound) pubnonce, using the SAME seed that produced `cp1`
		// so its re-derived nonce equals the `cp1` we aggregate against.
		let (hop_ctx, _) = channel_key_agg_ctx(&lp_pub, &hop_pub, &hop_pub).unwrap();
		let (hop_partial, hop_pn) = our_key_path_partial(
			hop_ctx, hop_idx, lp_idx, hop_sec, &[0xB1; 32], height, our_pn.clone(), msg,
		)
		.unwrap();
		assert_eq!(hop_pn.serialize(), cp1.serialize(), "hop re-derives the cp1 nonce");
		let (agg_ctx2, _) = channel_key_agg_ctx(&lp_pub, &hop_pub, &lp_pub).unwrap();
		let sig = aggregate_key_path_partials(
			agg_ctx2, msg, lp_idx, our_pn, our_partial, hop_idx, cp1, hop_partial,
		)
		.unwrap();
		secp.verify_schnorr(&sig, &Message::from_digest(msg), &q)
			.expect("bound-nonce counterparty partial still aggregates + verifies vs Q");
	}

	/// M9f #3 — RESTART DURABILITY (protocol level, not SGX sealing). On a
	/// ChannelManager reload the signer is RE-DERIVED (not deserialized): the
	/// vendored fork's `derive_channel_signer` reconstructs the inner
	/// `InMemorySigner` — hence the same `commitment_seed` (shachain root) — from the
	/// identical `channel_keys_id`, and the MuSig2 nonce is `f(root, height)` with
	/// nothing persisted. This test SIMULATES that reload: it derives a pubnonce +
	/// key-path partial "pre-reboot", then derives them AGAIN from ONLY the root +
	/// height ("post-reboot", fresh round objects, no carried state) and asserts (a)
	/// the re-derived pubnonce is byte-identical (no nonce reuse-with-different-value
	/// hazard, no nonce DB needed) AND (b) a partial signed post-reboot still
	/// aggregates with the peer's to a BIP340 sig verifying vs Q. Proves a force-
	/// close / commitment signature can be reproduced after a crash for a fixed
	/// (height, message) — the spec §1/§9f crash-safety guarantee.
	#[test]
	fn nonce_and_partial_reproduce_after_simulated_reload() {
		let secp = Secp256k1::new();
		let (lp_sec, lp_pub) = keypair(0x33);
		let (_hop_sec, hop_pub) = keypair(0x44);
		let lp_root = [0xEF; 32]; // the shachain root re-derived on reboot
		let height = 123_456u64;
		let msg = [0x9Au8; 32];

		// Peer (hop) nonce — stable for this fixed height (the peer re-derives it too).
		let (hop_ctx, hop_idx) = channel_key_agg_ctx(&lp_pub, &hop_pub, &hop_pub).unwrap();
		let hop_pn = local_pubnonce(hop_ctx, hop_idx, &[0x55; 32], height).unwrap();

		// "Pre-reboot": our local pubnonce for (root, height).
		let (lp_ctx_a, lp_idx) = channel_key_agg_ctx(&lp_pub, &hop_pub, &lp_pub).unwrap();
		let pn_before = local_pubnonce(lp_ctx_a, lp_idx, &lp_root, height).unwrap();

		// "Post-reboot": rebuild EVERYTHING from only (root, height) — fresh ctx, no
		// carried secnonce/round state — exactly what the re-derived signer does.
		let (lp_ctx_b, lp_idx_b) = channel_key_agg_ctx(&lp_pub, &hop_pub, &lp_pub).unwrap();
		let pn_after = local_pubnonce(lp_ctx_b, lp_idx_b, &lp_root, height).unwrap();
		assert_eq!(
			pn_before.serialize(),
			pn_after.serialize(),
			"re-derived MuSig2 nonce is identical after a reload (crash-safe, no nonce DB)"
		);

		// And the post-reboot partial still produces a valid aggregate sig.
		let (lp_ctx_c, _) = channel_key_agg_ctx(&lp_pub, &hop_pub, &lp_pub).unwrap();
		let (lp_partial, lp_pn) = our_key_path_partial(
			lp_ctx_c, lp_idx, hop_idx, lp_sec, &lp_root, height, hop_pn.clone(), msg,
		)
		.unwrap();
		assert_eq!(lp_pn.serialize(), pn_after.serialize(), "partial uses the same re-derived nonce");

		let (hop_sec, _) = keypair(0x44);
		let (hop_ctx2, _) = channel_key_agg_ctx(&lp_pub, &hop_pub, &hop_pub).unwrap();
		let (hop_partial, _) = our_key_path_partial(
			hop_ctx2, hop_idx, lp_idx, hop_sec, &[0x55; 32], height, pn_after.clone(), msg,
		)
		.unwrap();

		let (agg_ctx, _) = channel_key_agg_ctx(&lp_pub, &hop_pub, &lp_pub).unwrap();
		let q = aggregated_xonly(&agg_ctx);
		let (agg_ctx2, _) = channel_key_agg_ctx(&lp_pub, &hop_pub, &lp_pub).unwrap();
		let sig = aggregate_key_path_partials(
			agg_ctx2, msg, lp_idx, lp_pn, lp_partial, hop_idx, hop_pn, hop_partial,
		)
		.unwrap();
		secp.verify_schnorr(&sig, &Message::from_digest(msg), &q)
			.expect("post-reload aggregated key-path sig verifies vs Q");
	}
}
