/-!
# RLP specification

Recursive Length Prefix serialisation as the Ethereum Yellow Paper defines it in Appendix B
(`ethereum/yellowpaper`, `Paper.tex` at commit `efc5f9a1`, section "Recursive Length
Prefix"). Each definition below is one equation of that appendix, in the same order and with
the same case split; the empty set ∅ the paper returns for unencodable input is `none`.

The structure and names follow the ACL2 formalisation by Kestrel Institute
(`acl2/books/kestrel/ethereum/rlp`): `Tree` is `rlp-tree`, `encodeBytes` is
`rlp-encode-bytes`, `encodeTree` and `encodeTrees` are `rlp-encode-tree` and
`rlp-encode-tree-list`, and `encodeScalar` is `rlp-encode-scalar`. The decodability theorems
at the end are ACL2's `decodability.lisp`: every encoding function is injective over what it
can encode, and no tree encoding is a strict prefix of another. No Lean RLP formalisation
existed to reuse.
-/

namespace LeanLight.Spec.Rlp

abbrev Bytes := List UInt8

/--
𝕋 = 𝕃 ⊎ 𝔹: a byte array (a leaf), or a sequence of further structures (a branch). The
disjoint union keeps the empty byte array and the empty sequence apart.
-/
inductive Tree where
  | leaf (bytes : Bytes)
  | branch (subtrees : List Tree)

/-- BE(x): the big-endian byte array of minimal length whose value is `x`. BE(0) is empty. -/
def be (x : Nat) : Bytes :=
  if x = 0 then [] else be (x / 256) ++ [(x % 256).toUInt8]
decreasing_by omega

/-- R_b: the serialisation of a byte array, or `none` when it has 2^64 bytes or more. -/
def encodeBytes (x : Bytes) : Option Bytes :=
  if x.length = 1 ∧ x[0]?.getD 0 < 128 then some x
  else if x.length < 56 then some ((128 + x.length).toUInt8 :: x)
  else if x.length < 2 ^ 64 then some ((183 + (be x.length).length).toUInt8 :: (be x.length ++ x))
  else none

/-- R_l, given s(x): the serialisation of a sequence whose items serialise to `s`. -/
def encodeList (s : Bytes) : Option Bytes :=
  if s.length < 56 then some ((192 + s.length).toUInt8 :: s)
  else if s.length < 2 ^ 64 then some ((247 + (be s.length).length).toUInt8 :: (be s.length ++ s))
  else none

mutual
/-- RLP: the serialisation of a structure, or `none` when some part cannot be serialised. -/
def encodeTree : Tree → Option Bytes
  | .leaf x => encodeBytes x
  | .branch xs => (encodeTrees xs).bind encodeList

/-- s: the concatenated serialisations of a sequence's items, or `none` if any fails. -/
def encodeTrees : List Tree → Option Bytes
  | [] => some []
  | x :: xs => (encodeTree x).bind fun e => (encodeTrees xs).map (e ++ ·)
end

/-- RLP of a scalar: the serialisation of its minimal big-endian byte array. -/
def encodeScalar (i : Nat) : Option Bytes := encodeBytes (be i)

/-- s of a nonempty sequence: the first item's serialisation, then the rest's. -/
theorem encodeTrees_cons {t : Tree} {ts : List Tree} {e s : Bytes}
    (ht : encodeTree t = some e) (hs : encodeTrees ts = some s) :
    encodeTrees (t :: ts) = some (e ++ s) := by
  simp [encodeTrees, ht, hs]

/-! ## Big-endian representation -/

/-- The value of a big-endian byte array. -/
def beValue (bs : Bytes) : Nat := bs.foldl (fun acc b => acc * 256 + b.toNat) 0

theorem be_zero : be 0 = [] := by
  rw [be]; simp

theorem be_pos {x : Nat} (h : x ≠ 0) : be x = be (x / 256) ++ [(x % 256).toUInt8] := by
  rw [be]; simp [h]

theorem beValue_append_byte (bs : Bytes) (b : UInt8) :
    beValue (bs ++ [b]) = beValue bs * 256 + b.toNat := by
  simp [beValue, List.foldl_append]

theorem beValue_be (x : Nat) : beValue (be x) = x := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    by_cases hx : x = 0
    · subst hx; simp [be_zero, beValue]
    · rw [be_pos hx, beValue_append_byte, ih (x / 256) (by omega)]
      simp [Nat.toUInt8]
      omega

theorem be_injective {x y : Nat} (h : be x = be y) : x = y := by
  rw [← beValue_be x, ← beValue_be y, h]

theorem be_length_succ {x : Nat} (h : x ≠ 0) : (be x).length = (be (x / 256)).length + 1 := by
  rw [be_pos h]; simp

theorem be_ne_nil {x : Nat} (h : x ≠ 0) : be x ≠ [] := by
  rw [be_pos h]; simp

/-- BE of a value below 256^k has at most k bytes. -/
theorem be_length_le {x k : Nat} (h : x < 256 ^ k) : (be x).length ≤ k := by
  induction k generalizing x with
  | zero => simp at h; subst h; simp [be_zero]
  | succ k ih =>
    by_cases hx : x = 0
    · subst hx; simp [be_zero]
    · rw [be_length_succ hx]
      have : x / 256 < 256 ^ k := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]; rw [Nat.pow_succ] at h; exact h
      have := ih this
      omega

/-- A length below 2^64 has at most eight big-endian bytes. -/
theorem be_length_le_eight {x : Nat} (h : x < 2 ^ 64) : (be x).length ≤ 8 :=
  be_length_le (by simpa using h)

private theorem foldl_beValue (acc : Nat) (bs : Bytes) :
    bs.foldl (fun acc b => acc * 256 + b.toNat) acc = acc * 256 ^ bs.length + beValue bs := by
  induction bs generalizing acc with
  | nil => simp [beValue]
  | cons c cs ih =>
    have hc : beValue (c :: cs) = c.toNat * 256 ^ cs.length + beValue cs := by
      rw [beValue, List.foldl_cons, ih]; simp
    rw [List.foldl_cons, ih, hc, List.length_cons, Nat.pow_succ, Nat.add_mul, Nat.mul_assoc,
      Nat.mul_comm 256, Nat.add_assoc]

theorem beValue_cons (b : UInt8) (bs : Bytes) :
    beValue (b :: bs) = b.toNat * 256 ^ bs.length + beValue bs := by
  rw [beValue, List.foldl_cons, foldl_beValue]
  simp

theorem beValue_lt (bs : Bytes) : beValue bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [beValue]
  | cons c cs ih =>
    rw [beValue_cons, List.length_cons, Nat.pow_succ]
    have hc : c.toNat ≤ 255 := by have := c.toNat_lt; omega
    have : c.toNat * 256 ^ cs.length ≤ 255 * 256 ^ cs.length := Nat.mul_le_mul_right _ hc
    omega

/-- Leading zero bytes do not change a big-endian value. -/
theorem beValue_zero_cons (bs : Bytes) : beValue (0 :: bs) = beValue bs := by
  simp [beValue_cons]

private theorem beValue_pos {b : UInt8} {bs : Bytes} (hb : b ≠ 0) : 0 < beValue (b :: bs) := by
  rw [beValue_cons]
  have : 0 < b.toNat := by
    rcases Nat.eq_zero_or_pos b.toNat with h0 | h0
    · exact absurd (UInt8.toNat_inj.mp (by simpa using h0)) hb
    · exact h0
  have := Nat.mul_pos this (Nat.pow_pos (n := bs.length) (by omega : 0 < 256))
  omega

/-- A big-endian array with no leading zero is the minimal representation of its value. -/
theorem be_beValue : ∀ (n : Nat) (bs : Bytes), bs.length = n →
    (∀ b, bs.head? = some b → b ≠ 0) → be (beValue bs) = bs
  | 0, bs, hn, _ => by
    rw [List.length_eq_zero_iff.mp hn]; simp [beValue, be_zero]
  | n + 1, bs, hn, h => by
    rcases List.eq_nil_or_concat bs with rfl | ⟨init, c, rfl⟩
    · simp at hn
    rw [List.concat_eq_append] at h hn ⊢
    have hpos : beValue (init ++ [c]) ≠ 0 := by
      cases init with
      | nil =>
        have hc := h c (by simp)
        have := beValue_pos (bs := []) hc
        simpa using Nat.pos_iff_ne_zero.mp this
      | cons b rest =>
        have := beValue_pos (bs := rest ++ [c]) (h b (by simp))
        simpa using Nat.pos_iff_ne_zero.mp this
    rw [be_pos hpos, beValue_append_byte]
    have hc := c.toNat_lt
    rw [show (beValue init * 256 + c.toNat) / 256 = beValue init by omega,
      show (beValue init * 256 + c.toNat) % 256 = c.toNat by omega]
    have hinit : be (beValue init) = init := by
      cases init with
      | nil => simp [beValue, be_zero]
      | cons b rest =>
        exact be_beValue n (b :: rest) (by simp at hn ⊢; omega)
          (fun b' hb' => h b' (by simpa using hb'))
    rw [hinit]
    simp [Nat.toUInt8]

/-- Stripping leading zeros from a big-endian array gives the minimal representation. -/
theorem dropWhile_zero_eq_be (bs : Bytes) :
    bs.dropWhile (· == 0) = be (beValue bs) := by
  induction bs with
  | nil => simp [beValue, be_zero]
  | cons b rest ih =>
    by_cases hb : b = 0
    · subst hb
      simp [beValue_zero_cons, ih]
    · rw [List.dropWhile_cons_of_neg (by simpa using hb), be_beValue _ _ rfl]
      intro b' hb'
      simp at hb'
      exact hb' ▸ hb

/-! ## Decodability (ACL2 `decodability.lisp`) -/

/--
The length of the encoding at the front of `bs`, read from its first bytes as a decoder
does: the first byte says whether the length follows directly or as a big-endian number.
-/
def itemLength : Bytes → Nat
  | [] => 0
  | b :: rest =>
    if b.toNat < 128 then 1
    else if b.toNat < 184 then 1 + (b.toNat - 128)
    else if b.toNat < 192 then 1 + (b.toNat - 183) + beValue (rest.take (b.toNat - 183))
    else if b.toNat < 248 then 1 + (b.toNat - 192)
    else 1 + (b.toNat - 247) + beValue (rest.take (b.toNat - 247))

private theorem toUInt8_toNat {n : Nat} (h : n < 256) : n.toUInt8.toNat = n := by
  simp [Nat.toUInt8, Nat.mod_eq_of_lt h]

private theorem take_be_append (x : Nat) (s r : Bytes) :
    (be x ++ s ++ r).take (be x).length = be x := by
  simp

private theorem be_pos_length {x : Nat} (h : 0 < x) : 1 ≤ (be x).length := by
  have := be_ne_nil (Nat.pos_iff_ne_zero.mp h)
  cases hb : be x with
  | nil => exact absurd hb this
  | cons => simp

/-- What `encodeBytes` produces, case by case, with the facts a decoder relies on. -/
private theorem encodeBytes_cases {x e : Bytes} (h : encodeBytes x = some e) :
    (x.length = 1 ∧ x[0]?.getD 0 < 128 ∧ e = x) ∨
    (¬(x.length = 1 ∧ x[0]?.getD 0 < 128) ∧ x.length < 56 ∧ e = (128 + x.length).toUInt8 :: x) ∨
    (56 ≤ x.length ∧ x.length < 2 ^ 64 ∧
      e = (183 + (be x.length).length).toUInt8 :: (be x.length ++ x)) := by
  unfold encodeBytes at h
  split at h
  · rename_i hc; left; cases h; exact ⟨hc.1, hc.2, rfl⟩
  · rename_i hc; split at h
    · rename_i hl; right; left; cases h; exact ⟨hc, hl, rfl⟩
    · rename_i hl; split at h
      · rename_i hl'; right; right; cases h; exact ⟨by omega, hl', rfl⟩
      · contradiction

private theorem encodeList_cases {s e : Bytes} (h : encodeList s = some e) :
    (s.length < 56 ∧ e = (192 + s.length).toUInt8 :: s) ∨
    (56 ≤ s.length ∧ s.length < 2 ^ 64 ∧
      e = (247 + (be s.length).length).toUInt8 :: (be s.length ++ s)) := by
  unfold encodeList at h
  split at h
  · rename_i hl; left; cases h; exact ⟨hl, rfl⟩
  · rename_i hl; split at h
    · rename_i hl'; right; cases h; exact ⟨by omega, hl', rfl⟩
    · contradiction

/-- The first byte of a byte array's encoding is below 192 (ACL2 `car-of-rlp-encode-bytes`). -/
theorem encodeBytes_head {x e : Bytes} (h : encodeBytes x = some e) :
    ∃ b rest, e = b :: rest ∧ b.toNat < 192 := by
  rcases encodeBytes_cases h with ⟨h1, h2, he⟩ | ⟨-, h2, rfl⟩ | ⟨h1, h2, rfl⟩
  · rw [he]
    match x, h1 with
    | [b], _ =>
      simp [UInt8.lt_iff_toNat_lt] at h2
      exact ⟨b, [], rfl, by omega⟩
  · exact ⟨_, _, rfl, by rw [toUInt8_toNat (by omega)]; omega⟩
  · have := be_length_le_eight h2
    exact ⟨_, _, rfl, by rw [toUInt8_toNat (by omega)]; omega⟩

/-- The first byte of a sequence's encoding is at least 192. -/
theorem encodeList_head {s e : Bytes} (h : encodeList s = some e) :
    ∃ b rest, e = b :: rest ∧ 192 ≤ b.toNat := by
  rcases encodeList_cases h with ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩
  · exact ⟨_, _, rfl, by rw [toUInt8_toNat (by omega)]; omega⟩
  · have := be_length_le_eight h2
    exact ⟨_, _, rfl, by rw [toUInt8_toNat (by omega)]; omega⟩

/-- A byte array's encoding announces its own length (ACL2 `len-of-rlp-encode-bytes-from-prefix`). -/
theorem encodeBytes_itemLength {x e : Bytes} (h : encodeBytes x = some e) (r : Bytes) :
    itemLength (e ++ r) = e.length := by
  rcases encodeBytes_cases h with ⟨h1, h2, he⟩ | ⟨-, h2, rfl⟩ | ⟨h1, h2, rfl⟩
  · rw [he]
    match x, h1 with
    | [b], _ =>
      simp [UInt8.lt_iff_toNat_lt] at h2
      simp [itemLength, h2]
  · have hb := toUInt8_toNat (n := 128 + x.length) (by omega)
    simp only [itemLength, List.cons_append, hb, List.length_cons]
    rw [if_neg (by omega), if_pos (by omega)]
    omega
  · have h8 := be_length_le_eight h2
    have hpos := be_pos_length (x := x.length) (by omega)
    have hb := toUInt8_toNat (n := 183 + (be x.length).length) (by omega)
    simp only [itemLength, List.cons_append, hb, List.length_cons, List.length_append]
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    rw [show 183 + (be x.length).length - 183 = (be x.length).length by omega,
      List.append_assoc, List.take_left' rfl, beValue_be]
    omega

theorem encodeList_itemLength {s e : Bytes} (h : encodeList s = some e) (r : Bytes) :
    itemLength (e ++ r) = e.length := by
  rcases encodeList_cases h with ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩
  · have hb := toUInt8_toNat (n := 192 + s.length) (by omega)
    simp only [itemLength, List.cons_append, hb, List.length_cons]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    omega
  · have h8 := be_length_le_eight h2
    have hpos := be_pos_length (x := s.length) (by omega)
    have hb := toUInt8_toNat (n := 247 + (be s.length).length) (by omega)
    simp only [itemLength, List.cons_append, hb, List.length_cons, List.length_append]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [show 247 + (be s.length).length - 247 = (be s.length).length by omega,
      List.append_assoc, List.take_left' rfl, beValue_be]
    omega

/-- The payload of the encoding at the front of `bs`: what a decoder returns for it. -/
def payload : Bytes → Bytes
  | [] => []
  | b :: rest =>
    if b.toNat < 128 then [b]
    else if b.toNat < 184 then rest.take (b.toNat - 128)
    else if b.toNat < 192 then
      (rest.drop (b.toNat - 183)).take (beValue (rest.take (b.toNat - 183)))
    else if b.toNat < 248 then rest.take (b.toNat - 192)
    else (rest.drop (b.toNat - 247)).take (beValue (rest.take (b.toNat - 247)))

theorem encodeBytes_payload {x e : Bytes} (h : encodeBytes x = some e) (r : Bytes) :
    payload (e ++ r) = x := by
  rcases encodeBytes_cases h with ⟨h1, h2, he⟩ | ⟨-, h2, rfl⟩ | ⟨h1, h2, rfl⟩
  · rw [he]
    match x, h1 with
    | [b], _ =>
      simp [UInt8.lt_iff_toNat_lt] at h2
      simp [payload, h2]
  · have hb := toUInt8_toNat (n := 128 + x.length) (by omega)
    simp only [payload, List.cons_append, hb]
    rw [if_neg (by omega), if_pos (by omega)]
    simp
  · have h8 := be_length_le_eight h2
    have hpos := be_pos_length (x := x.length) (by omega)
    have hb := toUInt8_toNat (n := 183 + (be x.length).length) (by omega)
    simp only [payload, List.cons_append, hb]
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    rw [show 183 + (be x.length).length - 183 = (be x.length).length by omega,
      List.append_assoc, List.take_left' rfl, beValue_be, List.drop_left' rfl]
    simp

theorem encodeList_payload {s e : Bytes} (h : encodeList s = some e) (r : Bytes) :
    payload (e ++ r) = s := by
  rcases encodeList_cases h with ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩
  · have hb := toUInt8_toNat (n := 192 + s.length) (by omega)
    simp only [payload, List.cons_append, hb]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    simp
  · have h8 := be_length_le_eight h2
    have hpos := be_pos_length (x := s.length) (by omega)
    have hb := toUInt8_toNat (n := 247 + (be s.length).length) (by omega)
    simp only [payload, List.cons_append, hb]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [show 247 + (be s.length).length - 247 = (be s.length).length by omega,
      List.append_assoc, List.take_left' rfl, beValue_be, List.drop_left' rfl]
    simp

/-- R_b is injective over encodable byte arrays (ACL2 `rlp-encode-bytes-injective`). -/
theorem encodeBytes_injective {x y e : Bytes} (hx : encodeBytes x = some e)
    (hy : encodeBytes y = some e) : x = y := by
  rw [← encodeBytes_payload hx [], ← encodeBytes_payload hy []]

/-- R_l is injective over encodable payloads. -/
theorem encodeList_injective {s t e : Bytes} (hs : encodeList s = some e)
    (ht : encodeList t = some e) : s = t := by
  rw [← encodeList_payload hs [], ← encodeList_payload ht []]

theorem encodeTree_itemLength {t : Tree} {e : Bytes} (h : encodeTree t = some e) (r : Bytes) :
    itemLength (e ++ r) = e.length := by
  cases t with
  | leaf x => exact encodeBytes_itemLength h r
  | branch xs =>
    simp only [encodeTree] at h
    cases hs : encodeTrees xs with
    | none => simp [hs] at h
    | some s => rw [hs, Option.bind_some] at h; exact encodeList_itemLength h r

theorem encodeTree_ne_nil {t : Tree} {e : Bytes} (h : encodeTree t = some e) : e ≠ [] := by
  cases t with
  | leaf x =>
    obtain ⟨b, rest, rfl, -⟩ := encodeBytes_head h
    simp
  | branch xs =>
    simp only [encodeTree] at h
    cases hs : encodeTrees xs with
    | none => simp [hs] at h
    | some s =>
      rw [hs, Option.bind_some] at h
      obtain ⟨b, rest, rfl, -⟩ := encodeList_head h
      simp

private theorem encodeTree_leaf_branch {x : Bytes} {xs : List Tree} {e : Bytes}
    (hx : encodeTree (.leaf x) = some e) (hxs : encodeTree (.branch xs) = some e) : False := by
  obtain ⟨b, rest, rfl, hb⟩ := encodeBytes_head hx
  simp only [encodeTree] at hxs
  cases hs : encodeTrees xs with
  | none => simp [hs] at hxs
  | some s =>
    rw [hs, Option.bind_some] at hxs
    obtain ⟨b', rest', he, hb'⟩ := encodeList_head hxs
    cases he
    omega

mutual
/--
Two tree encodings followed by anything are equal only if the trees and the followers are:
an encoding is a self-delimiting prefix (the core of ACL2's `rlp-encode-tree-injective`).
-/
theorem encodeTree_append_inj : ∀ (t u : Tree) {e e' r r' : Bytes},
    encodeTree t = some e → encodeTree u = some e' → e ++ r = e' ++ r' → t = u ∧ r = r'
  | t, u, e, e', r, r', ht, hu, h => by
    have hlen : e.length = e'.length := by
      rw [← encodeTree_itemLength ht r, ← encodeTree_itemLength hu r', h]
    obtain ⟨rfl, rfl⟩ := List.append_inj h hlen
    refine ⟨?_, rfl⟩
    match t, u, ht, hu with
    | .leaf x, .leaf y, ht, hu => rw [encodeBytes_injective ht hu]
    | .leaf _, .branch _, ht, hu => exact (encodeTree_leaf_branch ht hu).elim
    | .branch _, .leaf _, ht, hu => exact (encodeTree_leaf_branch hu ht).elim
    | .branch xs, .branch ys, ht, hu =>
      simp only [encodeTree] at ht hu
      cases hxs : encodeTrees xs with
      | none => simp [hxs] at ht
      | some s =>
        cases hys : encodeTrees ys with
        | none => simp [hys] at hu
        | some s' =>
          rw [hxs, Option.bind_some] at ht
          rw [hys, Option.bind_some] at hu
          rw [encodeTrees_inj xs ys hxs (encodeList_injective hu ht ▸ hys)]

/-- s is injective over encodable sequences (ACL2 `rlp-encode-tree-list-injective`). -/
theorem encodeTrees_inj : ∀ (ts us : List Tree) {s : Bytes},
    encodeTrees ts = some s → encodeTrees us = some s → ts = us
  | [], [], _, _, _ => rfl
  | [], u :: us, s, hts, hus => by
    simp only [encodeTrees, Option.some.injEq] at hts
    subst hts
    simp only [encodeTrees] at hus
    cases hu : encodeTree u with
    | none => simp [hu] at hus
    | some e =>
      cases hus' : encodeTrees us with
      | none => simp [hu, hus'] at hus
      | some s' =>
        simp only [hu, hus', Option.bind_some, Option.map_some, Option.some.injEq] at hus
        exact absurd (List.append_eq_nil_iff.mp hus).1 (encodeTree_ne_nil hu)
  | t :: ts, [], s, hts, hus => by
    simp only [encodeTrees, Option.some.injEq] at hus
    subst hus
    simp only [encodeTrees] at hts
    cases ht : encodeTree t with
    | none => simp [ht] at hts
    | some e =>
      cases hts' : encodeTrees ts with
      | none => simp [ht, hts'] at hts
      | some s' =>
        simp only [ht, hts', Option.bind_some, Option.map_some, Option.some.injEq] at hts
        exact absurd (List.append_eq_nil_iff.mp hts).1 (encodeTree_ne_nil ht)
  | t :: ts, u :: us, s, hts, hus => by
    simp only [encodeTrees] at hts hus
    cases ht : encodeTree t with
    | none => simp [ht] at hts
    | some e =>
      cases hts' : encodeTrees ts with
      | none => simp [ht, hts'] at hts
      | some s₁ =>
        cases hu : encodeTree u with
        | none => simp [hu] at hus
        | some e' =>
          cases hus' : encodeTrees us with
          | none => simp [hu, hus'] at hus
          | some s₂ =>
            simp only [ht, hts', hu, hus', Option.bind_some, Option.map_some,
              Option.some.injEq] at hts hus
            obtain ⟨rfl, rfl⟩ := encodeTree_append_inj t u ht hu (hts.trans hus.symm)
            rw [encodeTrees_inj ts us hts' hus']
end

/-- RLP is injective over encodable trees (ACL2 `rlp-encode-tree-injective`). -/
theorem encodeTree_injective {t u : Tree} {e : Bytes} (ht : encodeTree t = some e)
    (hu : encodeTree u = some e) : t = u :=
  (encodeTree_append_inj t u (r := []) (r' := []) ht hu rfl).1

/-- No tree encoding is a strict prefix of another (ACL2 `rlp-encode-tree-unamb-prefix`). -/
theorem encodeTree_prefix {t u : Tree} {e e' : Bytes} (ht : encodeTree t = some e)
    (hu : encodeTree u = some e') (h : e <+: e') : e = e' := by
  obtain ⟨r, rfl⟩ := h
  have h1 := encodeTree_itemLength ht r
  have h2 := encodeTree_itemLength hu []
  rw [List.append_nil, h1, List.length_append] at h2
  have : r = [] := List.length_eq_zero_iff.mp (by omega)
  simp [this]

/-- The scalar encoding is injective (ACL2 `rlp-encode-scalar-injective`). -/
theorem encodeScalar_injective {i j : Nat} {e : Bytes} (hi : encodeScalar i = some e)
    (hj : encodeScalar j = some e) : i = j :=
  be_injective (encodeBytes_injective hi hj)

/-! ## Building encodings piece by piece -/

/-- s of a sequence with one more item at the end. -/
theorem encodeTrees_snoc {ts : List Tree} {t : Tree} {s e : Bytes}
    (hs : encodeTrees ts = some s) (ht : encodeTree t = some e) :
    encodeTrees (ts ++ [t]) = some (s ++ e) := by
  induction ts generalizing s with
  | nil => simp only [encodeTrees, Option.some.injEq] at hs; subst hs; simp [encodeTrees, ht]
  | cons u us ih =>
    simp only [encodeTrees] at hs
    cases hu : encodeTree u with
    | none => simp [hu] at hs
    | some eu =>
      cases hus : encodeTrees us with
      | none => simp [hu, hus] at hs
      | some sus =>
        simp only [hu, hus, Option.bind_some, Option.map_some, Option.some.injEq] at hs
        subst hs
        rw [List.cons_append, encodeTrees_cons hu (ih hus), List.append_assoc]

/-- s of two sequences one after the other. -/
theorem encodeTrees_append {ts us : List Tree} {s u : Bytes}
    (hs : encodeTrees ts = some s) (hu : encodeTrees us = some u) :
    encodeTrees (ts ++ us) = some (s ++ u) := by
  induction ts generalizing s with
  | nil => simp only [encodeTrees, Option.some.injEq] at hs; subst hs; simpa using hu
  | cons t ts ih =>
    simp only [encodeTrees] at hs
    cases ht : encodeTree t with
    | none => simp [ht] at hs
    | some et =>
      cases hts : encodeTrees ts with
      | none => simp [ht, hts] at hs
      | some sts =>
        simp only [ht, hts, Option.bind_some, Option.map_some, Option.some.injEq] at hs
        subst hs
        rw [List.cons_append, encodeTrees_cons ht (ih hts), List.append_assoc]

theorem encodeBytes_length_le {x e : Bytes} (h : encodeBytes x = some e) :
    e.length ≤ x.length + 9 := by
  rcases encodeBytes_cases h with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, h2, rfl⟩
  · omega
  · simp
  · have := be_length_le_eight h2
    simp; omega

theorem encodeList_length_le {s e : Bytes} (h : encodeList s = some e) :
    e.length ≤ s.length + 9 := by
  rcases encodeList_cases h with ⟨-, rfl⟩ | ⟨-, h2, rfl⟩
  · simp
  · have := be_length_le_eight h2
    simp; omega

theorem encodeScalar_length_le {n k : Nat} {e : Bytes} (hn : n < 256 ^ k)
    (h : encodeScalar n = some e) : e.length ≤ k + 9 := by
  have := encodeBytes_length_le h
  have := be_length_le hn
  omega

end LeanLight.Spec.Rlp
