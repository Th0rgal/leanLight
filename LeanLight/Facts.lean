import LeanLight.Anchor
import LeanLight.El.Mpt

/-!
# Facts at an anchored block (25k)

A fact is read from a proof under the state root of an EL header bound to an anchored beacon
header (`LeanLight.Anchor.bind`, 25j), and never from what the endpoint says it is: `ElProof`'s
response carries the endpoint's account fields beside the proof, and only the proof is read.

* LC6 reads accounts (`account`).
* LC7 reads a contract's code hash (`contract`: what a pin's code and a proxy's implementation
  are checked against) and storage (`storage`): the contract's account, then each slot's value
  under the account's storage root, the slots being the storage keys `Pins` derives (a pin's
  proxy and conditions, a token's balance, a pool's head and root). A slot the trie proves
  absent reads 0, as the EVM reads it. `storageAt` is the same reading under a state root given,
  without a header to bind: what the tests and the snapshot's token facts check against a root
  already bound.

`LeanLightProofs.Anchor` proves `account_spec`, `contract_spec`, `storageAt_spec` and
`storage_spec`: each is `Spec.Mpt`'s reading of the proofs under the root of the header `bind`
keeps. The wallet (leanKohakuDesktop) derives the storage keys it reads from its pin table; here the
caller names them.
-/

namespace LeanLight.Lc.Facts

open LeanLight.Lc.Forks (Chain)

/-- **An account fact (25k).** The account at `a`, read by `Spec.Mpt.accountB` from the proof's
`nodes` under the state root of the EL header `rlp`, once `Anchor.bind` keeps that header as the
block beacon header `b` names; with that header. -/
def account (c : Chain) (b : Store.Header) (rlp : ByteArray) (a : Anchor.Bytes)
    (nodes : ByteArray) : Option (Spec.Header.Header × Spec.Mpt.Account) :=
  match Anchor.bind c b rlp with
  | none => none
  | some h => (Spec.Mpt.accountB h.stateRoot a nodes).map fun acct => (h, acct)

/-- **A contract's code (25k).** The Keccak-256 of the code of the account at `a`, read as
`account` reads it (the empty code's hash for an account without code, or none at all); with the
header. -/
def contract (c : Chain) (b : Store.Header) (rlp : ByteArray) (a : Anchor.Bytes)
    (nodes : ByteArray) : Option (Spec.Header.Header × Anchor.Bytes) :=
  match account c b rlp a nodes with
  | none => none
  | some (h, acct) => some (h, acct.codeHash)

/-- The values of `slots`, each a storage key and the nodes of its proof, read one after the
other by `Spec.Mpt.storageB` under the storage root `root` (a slot proved absent reads 0), after
`acc` (newest first): a loop over at most a read's slots. -/
def valuesFrom (root : Anchor.Bytes) : List (Anchor.Bytes × ByteArray) → List Nat →
    Option (List Nat)
  | [], acc => some acc.reverse
  | (k, p) :: rest, acc =>
    match Spec.Mpt.storageB root k p with
    | none => none
    | some v => valuesFrom root rest (v :: acc)

/-- The values of `slots` under the storage root `root`, in their order; none when one proof
does not prove its slot. -/
def values (root : Anchor.Bytes) (slots : List (Anchor.Bytes × ByteArray)) : Option (List Nat) :=
  valuesFrom root slots []

/-- **Storage under a state root.** The account at `a`, read by `Spec.Mpt.accountB` from
`nodes` under the state root `root`, and the values of `slots` (each a storage key and the nodes
of its proof) under that account's storage root (`values`). No header is bound here: `storage`
binds one, and a snapshot's token fact is read under the root of the header its record binds. -/
def storageAt (root a : Anchor.Bytes) (nodes : ByteArray)
    (slots : List (Anchor.Bytes × ByteArray)) : Option (Spec.Mpt.Account × List Nat) :=
  match Spec.Mpt.accountB root a nodes with
  | none => none
  | some acct =>
    match values acct.storageRoot slots with
    | none => none
    | some vs => some (acct, vs)

/-- **A storage fact (25k).** The account at `a` and the values of `slots` under it, read as
`storageAt` reads them under the state root of the EL header `rlp`, once `Anchor.bind` keeps
that header as the block beacon header `b` names; with that header. The slots are the keys a
read asks (`Pins.pinSlots`, `tokenSlots`, `headSlots`, `rootSlot`), each with its proof's
nodes; a slot proved absent reads 0. -/
def storage (c : Chain) (b : Store.Header) (rlp : ByteArray) (a : Anchor.Bytes)
    (nodes : ByteArray) (slots : List (Anchor.Bytes × ByteArray)) :
    Option (Spec.Header.Header × Spec.Mpt.Account × List Nat) :=
  match Anchor.bind c b rlp with
  | none => none
  | some h =>
    match storageAt h.stateRoot a nodes slots with
    | none => none
    | some (acct, vs) => some (h, acct, vs)

end LeanLight.Lc.Facts
