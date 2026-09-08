# Vendored `rust-lightning` (LDK) — QU!D fork-of-a-fork

This directory is a **vendored copy** of the lexe LDK fork, pinned to:

    https://github.com/lexe-app/rust-lightning   branch lexe-v0.2.2-2026_04_28   (commit 027c6a1)

The workspace `[patch.crates-io]` in `quid-ln/Cargo.toml` points the `lightning*` crates at this path.

## ⛔ MEASURED 2026-09-08 — THIS FILE WAS DESCRIBING A DIFFERENT ARTEFACT

It said the tree was vendored *"so QU!D can carry a small, explicit local patch"*, told you to
*"treat everything here as upstream/read-only **except** changes tagged `QU!D PATCH`"*, and listed
**three** patches. All three of those statements are false, and the third is the one that misleads:

**A `diff -r` against the pinned upstream measures `+7,115 / −565` lines across 33 modified files,
plus one entirely new 548-line file (`lightning/src/sign/taproot_signer.rs`) — an 11,202-line patch.**
Only 29 lines anywhere in the tree carry a `QU!D PATCH` marker, so **grepping the marker finds well
under 1% of what we changed.**

Where the weight actually is (added/removed vs upstream):

| file | +/− | what it is |
|---|---|---|
| `ln/channel.rs` | +1526 / −250 | taproot channel state, splice signing, acceptor contribution |
| `ln/functional_tests.rs` | +1213 / −1 | |
| `ln/chan_utils.rs` | +1003 / −22 | taproot script/sighash builders |
| `sign/mod.rs` | +993 / −50 | the taproot signer trait surface |
| `sign/taproot_signer.rs` | +548 (new) | MuSig2 key-path partials |
| `ln/splicing_tests.rs` | +557 / −10 | |
| `chain/channelmonitor.rs` | +451 / −27 | the accessors this file *did* document |
| `chain/package.rs` | +377 / −4 | taproot on-chain resolution |
| `ln/msgs.rs` | +156 / −71 | |
| 25 more | | |

### 🔑 AND THE CORRECTION THAT MATTERS MOST: **SIMPLE-TAPROOT CHANNEL SUPPORT IS OURS, NOT LEXE'S.**

`QUEUE-KNOWLEDGE.md`'s §E174-r records the opposite — *"Simple-taproot support comes from the
**vendored LDK fork itself**… the fork carries `negotiate_simple_taproot` in `util/config.rs:242`…
taproot lives in the LDK codebase, not in those patches — **absence from a changelog is not absence
from the code**."* The reasoning was sound and the conclusion is wrong, because it was checked
against the vendored tree rather than against upstream. **Counted at commit `027c6a1`:**

| symbol | upstream `027c6a1` | this tree |
|---|---|---|
| `negotiate_simple_taproot` | **0** | 20 |
| `supports_simple_taproot` | **0** | 87 |
| `partially_sign_splice_shared_input` | **0** | 9 |
| `channel_taproot_script_pubkey` | **0** | 8 |
| `taproot_funding_aggregate_xonly` | **0** | 4 |
| `splice_nonce_height` | **0** | 9 |

Upstream also still has MuSig2 behind `[target.'cfg(taproot)'.dependencies]` on the dead
`arik-so/rust-musig2` (no taproot tweak). **We replaced it with `musig2 = "0.1.2"` in the DEFAULT
build.** ⇒ *"absence from a changelog is not absence from the code"* was right; the trap it missed is
that **presence in a vendored tree is not presence upstream** — the one comparison nobody ran.

⇒ **THIS IS NOT A PATCHED DEPENDENCY. IT IS A FORK, AND IT SHOULD LIVE IN ITS OWN REPO** — like the
other thirteen `github.com/quidmints/*` forks the workspace already uses (`rust-sgx`, `axum-server`,
`rust-esplora-client`, `hyper-util`, `mio`, `ring`, `tokio`). LDK is the one in-tree vendor exception,
and the exception was justified by a "small local patch" that does not exist.
▶️ **Owner ruling 2026-09-08: *"make any changes to ldk that are needed but that involves cloning our
fork repo and doing it there."*** ⚠️ **`quidmints/rust-lightning` DOES NOT EXIST YET** — probed over
SSH with a working control (`quidmints/tokio` resolves; the four candidate LDK names return
`Repository not found`). **Creating it is the prerequisite for any further LDK change.**

⚠️ **RE-VENDORING IS NO LONGER "re-copy and re-apply".** Upstream lexe is three releases ahead
(`lexe-v0.2.3-2026_07_21`, `a3ba0972`). Rebasing an 11,202-line patch is a project, not an errand.

## QU!D patches


### 1. `ChannelMonitor::funding_pubkeys()` — `lightning/src/chain/channelmonitor.rs`

Adds a public accessor returning the channel's two 2-of-2 funding pubkeys
`(holder, counterparty)`.

**Why:** `BTCChannels.openChannel` requires `OpenParams.{lpPubkey,hopPubkey}`
(the sorted 2-of-2 funding keys) at OPEN time. The funding output is a P2WSH
that hides the keys until the output is spent (channel close), so they can't be
read from chain at open. Upstream LDK exposes funding keys only through
`#[cfg(test/_test_utils)]` accessors (`do_mut_signer_call`,
`unsafe_get_latest_holder_commitment_txn`); nothing public maps a channel to its
funding pubkeys or `channel_keys_id`.

**Safety:** the funding pubkeys are PUBLIC, non-secret data (they appear in the
funding redeem script and are revealed on-chain at every close). Exposing a read
accessor leaks no key material. The Solidity side remains correct-by-construction
regardless: `ChannelLib.openChannelBody` independently rebuilds
`P2WSH(redeem(lp,hop))` and requires it to equal the on-chain funding output, so
a wrong/forged pubkey pair simply fails the contract check.

### 2. `ChannelContext::counterparty_shutdown_scriptpubkey()` + `ChannelDetails.counterparty_shutdown_scriptpubkey` — `lightning/src/ln/channel.rs`, `lightning/src/ln/channel_state.rs`

Adds a public getter on `ChannelContext` and a corresponding `Option<ScriptBuf>`
field on `ChannelDetails` (populated in `from_channel`, TLV id 49, optional) that
surface the counterparty's committed upfront shutdown script.

**Why:** `BTCChannels.recordClose` reads the LP's final balance from the
cooperative-close tx by summing outputs paying `P2WPKH(btcRecipientOf)`
(`_lpFinalBalance`). For that attribution to be correct, the LP's coop-close
payout must land on the script the EVM expects. The hop drives the hop-gated
`openChannel`, so it can refuse to register a channel whose LP payout script
won't conform — but only if it can READ the committed payout script. Upstream
LDK keeps `counterparty_shutdown_scriptpubkey` private to `ChannelContext`; no
public path (including `ChannelDetails`) exposes it.

**Safety:** the shutdown script is PUBLIC, non-secret data exchanged in
`open_channel`/`accept_channel` and revealed on-chain at every cooperative close.
Exposing a read accessor leaks no key material. It's purely additive (a new
optional field at an unused TLV id), so serialization stays backward-compatible.

Consumed by `quid-bridge::channel_driver::drive_open` (via
`quid-hop::node::channel_counterparty_shutdown_script`): the hop reads the LP's
committed P2WPKH shutdown script, derives its `HASH160`, and passes it to
`BTCChannels.openChannel`, which records it as `btcRecipientOf[lpEth]` — so the
LP's cooperative-close balance is attributed to exactly the output LDK pays it
to. Paired with `commit_upfront_shutdown_pubkey = true` (quid-hop node config),
which makes the script available at open and enforced unchanged at close.

### 3. `ChannelMonitor::original_funding_txo()` — `lightning/src/chain/channelmonitor.rs`

Adds a public accessor returning the channel's ORIGINAL (first-negotiated) funding
outpoint, which is STABLE across splices — unlike `get_funding_txo()`, which the
upstream docs say "will change for every splice that has reached its intended
confirmation depth."

**Why:** `BTCChannels` keys a channel's id on its ORIGINAL funding outpoint and
keeps that id across a SPLICE (which only rotates the live funding UTXO). The
bridge's channel reconciler iterates LDK monitors and recomputes each channel's
on-chain `channelId` to mirror open/close/splice. If it derived the id from
`get_funding_txo()` (the rotated, post-splice outpoint) it would mis-key every
spliced channel: it would read "not opened" and drive a PHANTOM second
`openChannel` (a double-count of the LP's BTC), and would never recognise the
channel's close. Upstream LDK keeps `first_negotiated_funding_txo` private with no
public accessor.

**Safety:** the funding outpoint is PUBLIC, non-secret data (it's an on-chain
txid:vout, visible whenever the funding tx confirms). Read-only; leaks no key
material; purely additive. Consumed by
`quid-bridge::channel_driver::run_channel_reconciler` to compute the stable on-chain
`channelId` (and to detect a splice the EVM mirror hasn't caught up to:
`ldk_value > on-chain amountSats` ⇒ re-drive `spliceChannel`).

## `ChannelMonitor::original_funding_pubkeys` (2026-08-31, §SPLICE-ROTATES-BOTH-FUNDING-KEYS)

Companion to the existing `original_funding_txo` / `first_negotiated_funding_txo` patch, added for
the same reason and because that patch stopped one step short.

**Why.** A splice rotates the funding *pubkeys* as well as the outpoint: `send_splice_init`
(`ln/channel.rs`) and the `splice_ack` handler each call
`ChannelSigner::new_funding_pubkey(prev_funding_txid)`, which tweaks the base funding key by
`SHA256(prev_funding_txid ‖ base_funding_secret)` (`sign/mod.rs`, `compute_funding_key_tweak`).
`ChannelMonitor::funding_pubkeys()` reads `self.funding.channel_parameters` — the **current** scope —
so it returns the rotated pair once a splice locks.

QU!D's `BTCChannels` derives `channelId` from the **original** pair and the **original** outpoint
(`ChannelLib.sol`, `openChannelBody`). `onchain_cid_from_monitor` therefore paired
`original_funding_txo()` with `funding_pubkeys()` and produced an id that changed at splice lock —
for a value its own docblock called STABLE. That id is the EVM channelId, the freshness /
anti-rollback anchor key (audit F3), and the persister's key.

**What.** `first_negotiated_funding_pubkeys: Option<(PublicKey, PublicKey)>` on `ChannelMonitorImpl`,
pinned at construction from `holder_pubkeys.funding_pubkey` and
`counterparty_channel_parameters.pubkeys.funding_pubkey` while `channel_parameters` still describes
the first funding scope. Persisted as **TLV type 39, `option`** in the monitor's write/read blocks
(37 was the previous highest; no collision). `(PublicKey, PublicKey)` round-trips as 66 fixed bytes
via `impl_tuple_ser!(a: A, b: B)`.

Accessor `ChannelMonitor::original_funding_pubkeys()` returns the pinned pair, falling back to
`funding_pubkeys()` when the field is absent — i.e. only for monitors written before this patch.
That fallback is correct for a never-spliced channel and wrong for a spliced one; there is no third
option, because the original pair was never persisted. The field is deliberately left `None` on read
rather than back-filled, so the fallback is visible at the accessor instead of a rotated pair
masquerading as the original.

**Non-secret**: funding pubkeys are revealed on-chain at funding.

⛔ Do not "simplify" `onchain_cid_from_monitor` back to `funding_pubkeys()`. The id must not follow
the channel's live scope — that is the entire reason `original_funding_txo` exists.

## Acceptor-side splice contribution (2026-09-01, §ACCEPTOR-CONTRIBUTION)

**Why.** `SpliceContribution::SpliceOut` removes value from the **initiator's** balance, and
`ChannelManager::internal_splice_init` hardcoded the acceptor's contribution to `0i64` under
*"TODO(splicing): Currently not possible to contribute on the splicing-acceptor side"*. Together those
force the party whose sats are leaving to drive the whole interactive-tx negotiation.

QU!D's swap-out delivery removes the **LP's** sats. The LP is an often-offline react-native wallet, and
**co-signing a splice is a far smaller ask of a wallet than driving one**. Upstream's own TODO inside
`Channel::splice_init` names this case: *"For always-on nodes this probably isn't a useful
optimization, but for often-offline nodes it may be, as we may connect and immediately go into
splicing from both sides."*

**What.** Every layer below the manager already supported it — `Channel::splice_init` takes an
`our_funding_contribution_satoshis`, `FundingNegotiationContext` carries the contribution *and*
`our_funding_outputs`, and `validate_splice_init` does not reject a non-zero acceptor contribution. So
the patch is small:

* `ChannelManager.pending_acceptor_contributions: Mutex<HashMap<ChannelId, SpliceContribution>>` —
  what this node will contribute to the next counterparty-initiated splice on that channel.
* `ChannelManager::register_acceptor_splice_contribution` / `clear_acceptor_splice_contribution`.
* `internal_splice_init` **removes** the registration and passes the resulting negative contribution
  plus its outputs to `Channel::splice_init`, which gained an `our_funding_outputs: Vec<TxOut>`
  parameter.

**Deliberate restrictions, each with its failure mode:**
* **One-shot** — the registration is consumed, so it cannot attach the same outputs to a later,
  unrelated splice. For a delivery that would pay a swapper twice out of a channel that never agreed.
* **Per-channel** — keyed by `ChannelId`, so an intent for one channel can never apply to another.
* **Not persisted** — restored on reload it would attach to whatever splice arrived next, possibly
  long after the delivery it belonged to was resolved. Re-register per attempt.
* **`SpliceOut` only** — a negative contribution is funded from channel balance and needs no inputs. A
  positive one needs inputs whose sufficiency the acceptor path still does not check (upstream's
  remaining TODO in `validate_splice_init`), so accepting one here would walk straight into that gap.
  A non-`SpliceOut` registration is refused when the splice arrives, and is **put back rather than
  dropped**, because silently discarding a registered intent is how a delivery goes missing.

**Upstream path is unchanged**: with no registration the contribution is `0i64` and
`our_funding_outputs` is empty, exactly as before.
