import LeanLightProofs.Anchor
import LeanLight.Driver

/-!
# A client's reads rest only on the checked steps

About `LeanLight.Driver`, what the command-line client calls with the bytes it fetched.

* `Reaches c root s`: the store `s` is one `Store.bootstrap` of checkpoint `root` starts and
  `Store.receive` steps carry, at any clocks and on any updates.
* `start_reaches`, `feed_reaches`: `start` gives only such stores and `feed` keeps a store such,
  whatever bytes the client hands them, in whatever order, as often as it likes.
* `read_sound`: a value `read` returns is read under the EL header
  `Anchor.bind` keeps for the store's anchor (whose RLP hashes to the anchored beacon header's
  execution block hash, `Anchor.bind_spec`), the account the trie's specification reads from the
  proof's nodes under that header's state root, each word the specification's storage read under
  the account's storage root (`Facts.storage_spec`).
* `codeOk_spec`: code accepted hashes to the proved code hash.

So what the client prints rests on the store's rules (bootstrap binds the checkpoint, acceptance
only after every check: `LeanLightProofs.Store`), `Anchor.bind`, and the trie, never on which
objects the unproved fetch loop asked for or how it ordered them. That loop decides only whether
a read happens and how fresh the anchor is.
-/

namespace LeanLight.Lc.Driver

open LeanLight.Lc.Forks (Chain)

/-- The stores reached from checkpoint `root`: one `Store.bootstrap` of it starts, then any
number of `Store.receive` steps, at any clocks, on any updates. -/
inductive Reaches (c : Chain) (root : ByteArray) : Store.Store → Prop
  | start {now : Nat} {b : Store.Bootstrap} {s : Store.Store} :
      Store.bootstrap c root now b = some s → Reaches c root s
  | step {s : Store.Store} (now : Nat) (u : Store.Update) :
      Reaches c root s → Reaches c root (Store.receive c s now u).1

/-- `start` gives only a store `Store.bootstrap` of the checkpoint starts. -/
theorem start_reaches {c : Chain} {root : ByteArray} {now : Nat} {tag : Codec.Tag}
    {bs : ByteArray} {s : Store.Store} (h : start c root now tag bs = some s) :
    Reaches c root s := by
  unfold start at h
  split at h
  · cases h
  · exact .start h

/-- `feed` keeps a store reached from the checkpoint reached from it, whatever its bytes. -/
theorem feed_reaches {c : Chain} {root : ByteArray} {s : Store.Store} (hs : Reaches c root s)
    (now : Nat) (k : Codec.Kind) (tag : Codec.Tag) (bs : ByteArray) :
    Reaches c root (feed c s now k tag bs).1 := by
  unfold feed
  split
  · exact hs
  · exact .step now _ hs

/-- **What a read returns is the checked steps' (the client's reads).** At any store, a value
`read` returns at clock `now` is read at the store's anchor `a`
(`Store.anchored`): under the EL header `h` that `Anchor.bind` keeps for `a`'s beacon header from
the endpoint's `rlp`, the account is what `Spec.Mpt.account` reads from the proof's `nodes` under
`h`'s state root, and the words are what `Spec.Mpt.storage` reads for each slot under the
account's storage root. Short of a Keccak-256 collision, those are the chain's values at the
block the anchor names (`Spec.MptTrie`, `Anchor.bind_spec`). The client reads only at stores
`start` and `feed` gave, so at stores reached from its checkpoint (`start_reaches`,
`feed_reaches`). -/
theorem read_sound {c : Chain} {s : Store.Store} {now : Nat} {rlp : ByteArray} {addr : List UInt8} {nodes : ByteArray}
    {slots : List (List UInt8 × ByteArray)} {h : Spec.Header.Header} {acct : Spec.Mpt.Account}
    {vs : List Nat} (hr : read c s now rlp addr nodes slots = some (h, acct, vs)) :
    ∃ a, Store.anchored c s now = some a ∧ Anchor.bind c a.header rlp = some h ∧
      Spec.Mpt.account h.stateRoot addr nodes.data.toList = some acct ∧
      slots.map (fun x => Spec.Mpt.storage acct.storageRoot x.1 x.2.data.toList) = vs.map some := by
  unfold read at hr
  split at hr
  · cases hr
  · rename_i a ha
    exact ⟨a, ha, Facts.storage_spec hr⟩

/-- `bindAnchor` binds an EL header only to the store's anchor, as `Anchor.bind` does. -/
theorem bindAnchor_sound {c : Chain} {s : Store.Store} {now : Nat} {rlp : ByteArray}
    {b : Store.Header} {h : Spec.Header.Header} (hb : bindAnchor c s now rlp = some (b, h)) :
    ∃ a, Store.anchored c s now = some a ∧ a.header = b ∧ Anchor.bind c b rlp = some h := by
  unfold bindAnchor at hb
  split at hb
  · cases hb
  · rename_i a ha
    cases hbind : Anchor.bind c a.header rlp with
    | none => simp [hbind] at hb
    | some h' =>
      simp only [hbind, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨a, ha, rfl, hbind⟩

/-- Code `codeOk` accepts hashes to the account's proved code hash. -/
theorem codeOk_spec {acct : Spec.Mpt.Account} {code : ByteArray} (h : codeOk acct code = true) :
    Spec.Common.keccak code.data.toList = acct.codeHash := by
  simpa [codeOk] using h

end LeanLight.Lc.Driver
