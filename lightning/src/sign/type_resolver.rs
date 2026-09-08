use crate::sign::{ChannelSigner, SignerProvider};
use core::ops::Deref;

pub(crate) enum ChannelSignerType<SP: Deref>
where
	SP::Target: SignerProvider,
{
	// in practice, this will only ever be an EcdsaChannelSigner (specifically, Writeable)
	Ecdsa(<SP::Target as SignerProvider>::EcdsaSigner),
	#[allow(unused)]
	Taproot(<SP::Target as SignerProvider>::TaprootSigner),
}

impl<SP: Deref> ChannelSignerType<SP>
where
	SP::Target: SignerProvider,
{
	pub(crate) fn as_ref(&self) -> &dyn ChannelSigner {
		match self {
			ChannelSignerType::Ecdsa(ecs) => ecs,
			#[allow(unused)]
			ChannelSignerType::Taproot(tcs) => tcs,
		}
	}

	#[allow(unused)]
	pub(crate) fn as_ecdsa(&self) -> Option<&<SP::Target as SignerProvider>::EcdsaSigner> {
		match self {
			ChannelSignerType::Ecdsa(ecs) => Some(ecs),
			_ => None,
		}
	}

	#[allow(unused)]
	pub(crate) fn as_mut_ecdsa(
		&mut self,
	) -> Option<&mut <SP::Target as SignerProvider>::EcdsaSigner> {
		match self {
			ChannelSignerType::Ecdsa(ecs) => Some(ecs),
			_ => None,
		}
	}

	/// Borrow the inner taproot (MuSig2) signer, if this is a taproot channel.
	/// Used by the simple-taproot-channel (M6) nonce-exchange handler to generate
	/// the local `next_local_nonce` and drive key-path partial signing.
	#[allow(unused)]
	pub(crate) fn as_taproot(&self) -> Option<&<SP::Target as SignerProvider>::TaprootSigner> {
		match self {
			ChannelSignerType::Taproot(tcs) => Some(tcs),
			_ => None,
		}
	}
}
