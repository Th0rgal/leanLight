import LeanLight.Base.Keccak
import LeanLight.Base.KeccakFast
import LeanLight.Base.Rlp
import LeanLight.Bytes
import LeanLight.El.Rlp

/-!
# Ordered trie roots, built (LC8, G12)

The root of the Merkle-Patricia trie of an ordered list, the transactions' or the receipts' of
a block (`transactionsRoot`, `receiptsRoot`): item `i`, its encoding, under the key `rlp(i)`
(leanKohakuDesktop's `spec/16-light-client.md`, "Inclusion and receipts"). The items are the payloads of byte
strings found in one buffer (`Span`s, as `itemsAtB` finds them in netd's re-encoded list), and
are never copied into lists.

The construction is the Yellow Paper's (Appendix D), as `LeanLightProofs.Spec.MptTrie` models it,
step for step: the structural composition function c(𝔍, i) (`compose`: a leaf, an extension
over the keys' common prefix, or a branch of the sixteen groups by the next nibble with the
value of a key that ends there) and the node cap function n(𝔍, i) (`cap`). It differs in what it
builds: `node` returns c(𝔍, i)'s RLP as a `ByteArray`, and a parent embeds `ref` of it, the RLP
of n(𝔍, i): the RLP itself when shorter than 32 bytes, else the RLP of its Keccak-256.
`LeanLightProofs.Trie` proves `node`'s RLP that of `Spec.Mpt.Trie.compose` of the same data
(`node_eq`) and `orderedRoot` `Spec.Mpt.Trie.root` of the ordered map (`orderedRoot_eq`).

Recursion: `node` calls itself once a level of the trie, on the same keys further on or on the
keys of one nibble, so its depth is at most a key's nibbles plus one: an item's key `rlp(i)` has
at most 18 nibbles for any index below 2^64. Over the items it loops with `List.filter`,
`List.foldl`, `List.find?`, `List.map` and `List.zipIdx`, which Lean core runs in constant stack
(the keys' common prefix is a left fold of `lcp`, where the model's `common` recurses on the
list). The Keccak-256 and the copies are of each node once: about the items' bytes plus 40
bytes an item.
-/

namespace LeanLight.Lc.Trie

open LeanLight.Spec.Rlp (be encodeScalar)
open LeanLight.Spec.RlpDecode (Span)

/-- A key as nibbles, each below 16. -/
abbrev Nibbles := List Nat

/-- The longest common prefix of two nibble lists. -/
def lcp : Nibbles → Nibbles → Nibbles
  | a :: x, b :: z => if a = b then a :: lcp x z else []
  | _, _ => []

/-- Nibbles packed two by two, high nibble first. -/
def pack : Nibbles → List UInt8
  | a :: b :: rest => (16 * a + b).toUInt8 :: pack rest
  | _ => []

/-- The hex-prefix encoding of a path (Yellow Paper, Appendix C): a flag nibble, 2 for a leaf
plus 1 for an odd number of nibbles, then the nibbles packed. -/
def hp (x : Nibbles) (t : Bool) : List UInt8 :=
  let flag := if t then 2 else 0
  if x.length % 2 = 0 then (16 * flag).toUInt8 :: pack x
  else (16 * (flag + 1) + x.headD 0).toUInt8 :: pack x.tail

/-- A byte list's nibbles, high nibble first. -/
def nibbles (bs : List UInt8) : Nibbles := bs.flatMap fun b => [b.toNat / 16, b.toNat % 16]

/-- Keys with their items, in order. -/
abbrev Obj := List (Nibbles × Span)

/-- The longest prefix all the keys share, a left fold of `lcp`. -/
def common : Obj → Nibbles
  | [] => []
  | e :: rest => rest.foldl (fun c kv => lcp c kv.1) e.1

/-- The keys whose nibble `i` is `x`, in order. -/
def sub (obj : Obj) (i x : Nat) : Obj := obj.filter fun e => e.1[i]? = some x

/-- The item of the first key of `i` nibbles, if any. -/
def terminal (obj : Obj) (i : Nat) : Option Span := (obj.find? fun e => e.1.length = i).map (·.2)

/-- What `node`'s recursion decreases: the nibbles left after `i`, plus one a key. -/
def measure (obj : Obj) (i : Nat) : Nat := (obj.map fun kv => kv.1.length - i + 1).sum

theorem lcp_length_le_left : ∀ (a b : Nibbles), (lcp a b).length ≤ a.length
  | a :: x, b :: z => by
    simp only [lcp]; split
    · have := lcp_length_le_left x z; simp; omega
    · simp
  | [], _ => by simp [lcp]
  | _ :: _, [] => by simp [lcp]

theorem lcp_length_le_right : ∀ (a b : Nibbles), (lcp a b).length ≤ b.length
  | a :: x, b :: z => by
    simp only [lcp]; split
    · have := lcp_length_le_right x z; simp; omega
    · simp
  | [], _ => by simp [lcp]
  | _ :: _, [] => by simp [lcp]

theorem foldl_lcp_le : ∀ (l : Obj) (c : Nibbles),
    (l.foldl (fun c kv => lcp c kv.1) c).length ≤ c.length ∧
      ∀ f ∈ l, (l.foldl (fun c kv => lcp c kv.1) c).length ≤ f.1.length
  | [], c => ⟨Nat.le_refl _, fun f h => by simp at h⟩
  | g :: l, c => by
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := foldl_lcp_le l (lcp c g.1)
    refine ⟨Nat.le_trans h1 (lcp_length_le_left _ _), fun f hf => ?_⟩
    rcases List.mem_cons.mp hf with rfl | hf
    · exact Nat.le_trans h1 (lcp_length_le_right _ _)
    · exact h2 f hf

/-- The common prefix is no longer than any key. -/
theorem common_le : ∀ (obj : Obj), ∀ f ∈ obj, (common obj).length ≤ f.1.length
  | [], _, h => by simp at h
  | e :: rest, f, h => by
    obtain ⟨h1, h2⟩ := foldl_lcp_le rest e.1
    rcases List.mem_cons.mp h with rfl | h
    · exact h1
    · exact h2 f h

theorem measure_extension {obj : Obj} {i j : Nat} (hne : obj ≠ []) (hij : i < j)
    (hj : ∀ f ∈ obj, j ≤ f.1.length) : measure obj j < measure obj i := by
  induction obj with
  | nil => exact absurd rfl hne
  | cons e rest ih =>
    have he := hj e (by simp)
    simp only [measure, List.map_cons, List.sum_cons] at ih ⊢
    by_cases hr : rest = []
    · subst hr; simp; omega
    · have := ih hr (fun f hf => hj f (by simp [hf])); omega

theorem measure_sub_le (i x : Nat) : ∀ (obj : Obj),
    measure (sub obj i x) (i + 1) + obj.length ≤ measure obj i
  | [] => Nat.le_refl _
  | kv :: rest => by
    have ih := measure_sub_le i x rest
    simp only [sub, List.filter_cons] at ih ⊢
    split
    · rename_i h
      have hl : i < kv.1.length := (List.getElem?_eq_some_iff.mp (of_decide_eq_true h)).1
      simp only [measure, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
      omega
    · simp only [measure, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
      omega

theorem measure_sub {kv : Nibbles × Span} {rest : Obj} (i x : Nat) :
    measure (sub (kv :: rest) i x) (i + 1) < measure (kv :: rest) i := by
  have := measure_sub_le i x (kv :: rest)
  simp only [List.length_cons] at this
  omega

/-! ## RLP into a `ByteArray` -/

/-- The bytes before a payload of `n` bytes: `offset` is 128 for a byte string (R_b), 192 for a
list (R_l); `none` from 2^64 bytes, which RLP cannot write. -/
def head (offset n : Nat) : Option ByteArray :=
  if n < 56 then some ⟨#[(offset + n).toUInt8]⟩
  else if n < 18446744073709551616 then
    some ⟨((offset + 55 + (be n).length).toUInt8 :: be n).toArray⟩
  else none

/-- R_b: a byte string's RLP. -/
def encBytes (x : ByteArray) : Option ByteArray :=
  if x.size = 1 ∧ x[0]?.getD 0 < 128 then some x else (head 128 x.size).map (· ++ x)

/-- R_l: the RLP of a list whose items' RLP, one after the other, is `s`. -/
def encList (s : ByteArray) : Option ByteArray := (head 192 s.size).map (· ++ s)

/-- What a parent embeds for a node whose RLP is `e`: `e` itself when shorter than 32 bytes,
else the RLP of its Keccak-256. -/
def ref (e : ByteArray) : ByteArray :=
  if e.size < 32 then e else ⟨#[0xa0]⟩ ++ Spec.Keccak.keccak256 e

/-- The item `s` of `bs`: the bytes from its payload's start to its end. -/
def valueOf (bs : ByteArray) (s : Span) : ByteArray := Bytes.extract bs s.start s.stop

/-- A branch's value: the item's, or the empty string. -/
def valueOrEmpty (bs : ByteArray) : Option Span → ByteArray
  | some s => valueOf bs s
  | none => .empty

/-! ## The construction -/

/-- The RLP of c(𝔍, i), the node of the keys of `obj` (which share their first `i` nibbles),
their items in `bs`: `0x80` for no key; one key, a leaf; a prefix all keys share past `i`, an
extension; otherwise a branch of the sixteen groups by nibble `i`. `none` where an RLP cannot be
written. -/
def node (bs : ByteArray) : Obj → Nat → Option ByteArray
  | [], _ => some ⟨#[0x80]⟩
  | [(k, v)], i => do
    let path ← encBytes ⟨(hp (k.drop i) true).toArray⟩
    let value ← encBytes (valueOf bs v)
    encList (path ++ value)
  | e :: e' :: rest, i =>
    if i < (common (e :: e' :: rest)).length then do
      let path ← encBytes ⟨(hp ((common (e :: e' :: rest)).drop i) false).toArray⟩
      let sub ← node bs (e :: e' :: rest) (common (e :: e' :: rest)).length
      encList (path ++ ref sub)
    else do
      let subnodes ← (List.range 16).foldlM (fun acc x => do
          let s ← node bs (sub (e :: e' :: rest) i x) (i + 1)
          pure (acc ++ ref s)) ByteArray.empty
      let value ← encBytes (valueOrEmpty bs (terminal (e :: e' :: rest) i))
      encList (subnodes ++ value)
termination_by obj i => measure obj i
decreasing_by
  · exact measure_extension (List.cons_ne_nil _ _) (by assumption) (common_le _)
  · exact measure_sub i x

/-- The root of the trie of `obj`: Keccak-256 of its root node's RLP. -/
def root (bs : ByteArray) (obj : Obj) : Option ByteArray :=
  (node bs obj 0).map Spec.Keccak.keccak256

/-- The key of item `i`: its index's RLP (`rlp.encode(Uint(i))`), as nibbles. -/
def indexNibbles (i : Nat) : Nibbles := nibbles ((encodeScalar i).getD [])

/-- **The root of an ordered list's trie**: item `i` of `items` under `rlp(i)`, each item the
payload `items` locates in `bs`. -/
def orderedRoot (bs : ByteArray) (items : List Span) : Option ByteArray :=
  root bs (items.zipIdx.map fun vi => (indexNibbles vi.2, vi.1))

end LeanLight.Lc.Trie
