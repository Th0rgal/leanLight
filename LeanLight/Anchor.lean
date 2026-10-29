import LeanLight.Store
import LeanLight.El.Header

/-!
# Anchoring execution reads: the EL header, by hash (25j)

An anchored beacon header names an EL block by its hash (`Store.Header.elHash`), tagged by the
header's own slot (`Store.elTag`, spec/16 "Objects"): `Own`, the block's own payload hash (an
Electra or Fulu header's `execution.block_hash`, or a pre-Gloas header brought into a Gloas
container), or `Parent`, from `GLOAS_FORK_EPOCH` on, the parent payload's
(`signed_execution_payload_bid.message.parent_block_hash`). `bind` takes the EL header's RLP,
fetched by that hash (`eth_getBlockByHash`, netd's re-encoding, untrusted), and keeps it only
when it is that block (`docs/spec-16-light-client.md`, "The EL header, by hash"):

* always: `keccak(rlp)` is the hash and the RLP is a known fork's header (`Spec.Header.verifyB`,
  14b), so every field read below is the hashed header's;
* `Own`: its timestamp is `slotTime(slot) / 1000` and its `parentBeaconBlockRoot` (field 19,
  EIP-4788) the beacon block's `parent_root`; for an Electra-typed header also
  `execution_matches`: state root, number, gas limit, gas used, timestamp, base fee and receipts
  root (field 5) equal the payload header's. An upgraded header carries no payload fields: the
  Keccak binding makes them redundant;
* `Parent`, by the parent's own EL fork: an Amsterdam header (23 fields) has `slotNumber`
  (field 22, EIP-7843) `< slot` and its timestamp is `slotTime(slotNumber) / 1000`
  (`gloas/fork-choice.md`); an earlier one, which the first Gloas blocks build on, has a
  timestamp before the Gloas fork's, the time of a slot `k < slot` (`k` is `slotOf` of it).

`Spec.Header.Header` reads fields 0, 3, 8 to 11 and 15; the binding reads 5, 19 and 22 here
(`fieldsB`, `extraOf`) from the same field list `decodeB` reads, so 14b's statements and
`lkd_verified::header` are unchanged. `LeanLightProofs.Anchor` proves what `bind` accepts
(`bind_spec`). The payload header's `transactions_root` is an SSZ root, not the EL trie's, and is
not compared.
-/

namespace LeanLight.Lc.Anchor

open LeanLight.Spec.RlpDecode (itemAtB itemsAtB)
open LeanLight.Lc.Forks (Chain)

/-- Bytes as lists, as the EL readers keep them. -/
abbrev Bytes := List UInt8

/-- The field list of an EL header's RLP, read where `Spec.Header.decodeB` reads it: one
canonical list spanning the bytes, whose items are byte arrays. `decodeB` is `ofFields` of this
list (`LeanLightProofs.Anchor.decodeB_fieldsB`). -/
def fieldsB (bs : ByteArray) : Option (List Bytes) :=
  match itemAtB bs 0 bs.size with
  | none => none
  | some top =>
    if top.list = true ∧ top.stop = bs.size then
      match itemsAtB bs top.start top.stop with
      | none => none
      | some its =>
        if its.all (fun it => !it.list) then some (its.map (Spec.Header.payloadOfB bs)) else none
    else none

/-- What the binding reads beyond `Spec.Header.Header`: the receipts root (field 5), the
`parentBeaconBlockRoot` (field 19, from Cancun on) and the `slotNumber` (field 22, Amsterdam). -/
structure Extra where
  receiptsRoot : Bytes
  parentBeaconBlockRoot : Option Bytes
  slotNumber : Option Nat

/-- The fields `Extra` names, of a field list. -/
def extraOf (fs : List Bytes) : Extra :=
  { receiptsRoot := Spec.Header.field fs 5
    parentBeaconBlockRoot := if 20 ≤ fs.length then some (Spec.Header.field fs 19) else none
    slotNumber := if 23 ≤ fs.length then some (Spec.Rlp.beValue (Spec.Header.field fs 22))
      else none }

/-- `execution_matches`, for an Electra-typed header's payload: the state root, number, gas
limit, gas used, timestamp, base fee and receipts root equal the EL header's. -/
def execMatches (e : Ssz.ExecutionPayloadHeader) (h : Spec.Header.Header) (x : Extra) : Bool :=
  e.stateRoot.data.toList == h.stateRoot && e.blockNumber == h.number &&
    e.gasLimit == h.gasLimit && e.gasUsed == h.gasUsed && e.timestamp == h.timestamp &&
    e.baseFeePerGas == h.baseFee && e.receiptsRoot.data.toList == x.receiptsRoot

/-- The checks of an `Own` hash: the EL block's timestamp is its beacon block's slot's time, in
seconds, and its `parentBeaconBlockRoot` (EIP-4788) is that block's parent root. -/
def ownOk (c : Chain) (b : Ssz.BeaconBlockHeader) (h : Spec.Header.Header) (x : Extra) : Bool :=
  h.timestamp == c.slotTime b.slot / 1000 &&
    x.parentBeaconBlockRoot == some b.parentRoot.data.toList

/-- The checks of a `Parent` hash, from a beacon block at `slot`, by the parent's own EL fork:
an Amsterdam header's `slotNumber` is before `slot` and its timestamp that slot's time; an
earlier header's timestamp is before the Gloas fork's and is the time of a slot before `slot`. -/
def parentOk (c : Chain) (slot : Nat) (h : Spec.Header.Header) (x : Extra) : Bool :=
  match x.slotNumber with
  | some n => decide (n < slot) && h.timestamp == c.slotTime n / 1000
  | none =>
    match c.gloasEpoch with
    | some e =>
      let k := c.slotOf (h.timestamp * 1000)
      decide (h.timestamp < c.slotTime (c.startSlot e) / 1000) && decide (k < slot) &&
        h.timestamp == c.slotTime k / 1000
    | none => false

/-- Whether an EL header `h`, `x` its other fields, is the block beacon header `b` names, beyond
its hash: by `b`'s tag, `Own` (with `execution_matches` for an Electra-typed header) or
`Parent`. -/
def fieldsOk (c : Chain) (b : Store.Header) (h : Spec.Header.Header) (x : Extra) : Bool :=
  match Store.elTag c b with
  | .own =>
    (match b.exec with
      | .payload e => execMatches e h x
      | .blockHash _ => true) && ownOk c b.beacon h x
  | .parent => parentOk c b.beacon.slot h x

/-- **The EL binding (25j).** The EL header whose RLP is `rlp`, kept only when it is the block
beacon header `b` names: Keccak-256 of `rlp` is `b`'s EL hash, `rlp` is a known fork's header
(`Spec.Header.verifyB`), and its fields pass `fieldsOk`. -/
def bind (c : Chain) (b : Store.Header) (rlp : ByteArray) : Option Spec.Header.Header :=
  match Spec.Header.verifyB rlp b.elHash.data.toList with
  | none => none
  | some h =>
    match fieldsB rlp with
    | none => none
    | some fs => if fieldsOk c b h (extraOf fs) then some h else none

end LeanLight.Lc.Anchor
