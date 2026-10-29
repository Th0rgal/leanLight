import LeanLight.El.Rlp

/-!
# RLP decoding specification: whole structures

`LeanLight.El.Rlp` decodes one item at a time, canonically (`decodeHead`, `itemAt`, `itemsAt`);
that is what runs. Here `decodeTree` decodes a whole structure, and `decodeTree_encodeTree`,
`encodeTree_decodeTree` lift the round trip to `Spec.Rlp.encodeTree`: a structure is decoded
from its encoding, and what decodes is the encoding of the structure decoded. `decodeTree`
recurses with the nesting, through fuel `2·|w|+1` that grows with the input; it is a
specification, never compiled into the wallet (AGENTS.md, Runtime Lean), and so lives here and
not in `proofs/core`.
-/

namespace LeanLight.Spec.RlpDecode

open LeanLight.Spec.Rlp

mutual
/-- The structure `w` encodes, exactly: `none` unless `w` is one canonical item whose list
payloads, at every depth, are canonical items exactly. `n` is fuel. -/
def decodeTreeF : Nat → Bytes → Option Tree
  | 0, _ => none
  | n + 1, w =>
    match decodeHead w with
    | none => none
    | some h =>
      if h.size = w.length then
        if h.list then (decodeListF n (payload w h)).map .branch
        else some (.leaf (payload w h))
      else none

/-- The structures a list payload encodes, one after the other. -/
def decodeListF : Nat → Bytes → Option (List Tree)
  | 0, _ => none
  | _ + 1, [] => some []
  | n + 1, b :: bs =>
    match decodeHead (b :: bs) with
    | none => none
    | some h =>
      match decodeTreeF n ((b :: bs).take h.size), decodeListF n ((b :: bs).drop h.size) with
      | some t, some ts => some (t :: ts)
      | _, _ => none
end

/-- The structure `w` encodes, or `none` unless `w` is its canonical encoding. -/
def decodeTree (w : Bytes) : Option Tree := decodeTreeF (2 * w.length + 1) w

private theorem encodeTree_ne_nil' {t : Tree} {e : Bytes} (h : encodeTree t = some e) :
    e ≠ [] := encodeTree_ne_nil h

mutual
theorem decodeTreeF_encodeTree : ∀ (t : Tree) {e : Bytes} {n : Nat},
    encodeTree t = some e → 2 * e.length < n → decodeTreeF n e = some t
  | .leaf x, e, n, h, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h' : encodeItem false x = some e := h
    have hd := decodeHead_encodeItem h' []
    rw [List.append_nil] at hd
    obtain ⟨hle, hdrop⟩ := encodeItem_suffix h'
    simp only [decodeTreeF, hd, Head.size, Bool.false_eq_true, if_false]
    rw [if_pos (by omega)]
    simp [payload, hdrop]
  | .branch ts, e, n, h, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [encodeTree] at h
    cases hs : encodeTrees ts with
    | none => simp [hs] at h
    | some s =>
      rw [hs, Option.bind_some] at h
      have h' : encodeItem true s = some e := h
      have hd := decodeHead_encodeItem h' []
      rw [List.append_nil] at hd
      obtain ⟨hle, hdrop⟩ := encodeItem_suffix h'
      have hlt := encodeList_length h
      simp only [decodeTreeF, hd, Head.size, if_true]
      rw [if_pos (by omega)]
      have hp : payload e ⟨true, e.length - s.length, s.length⟩ = s := by simp [payload, hdrop]
      rw [hp, decodeListF_encodeTrees ts hs (by omega)]
      rfl

theorem decodeListF_encodeTrees : ∀ (ts : List Tree) {s : Bytes} {n : Nat},
    encodeTrees ts = some s → 2 * s.length + 1 < n → decodeListF n s = some ts
  | [], s, n, h, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [encodeTrees, Option.some.injEq] at h
    subst h
    rfl
  | t :: ts, s, n, h, hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [encodeTrees] at h
    cases ht : encodeTree t with
    | none => simp [ht] at h
    | some e =>
      cases hts : encodeTrees ts with
      | none => simp [ht, hts] at h
      | some s' =>
        simp only [ht, hts, Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        have hne := encodeTree_ne_nil' ht
        have hdh : ∃ l p, encodeItem l p = some e := by
          cases t with
          | leaf x => exact ⟨false, x, ht⟩
          | branch us =>
            simp only [encodeTree] at ht
            cases hus : encodeTrees us with
            | none => simp [hus] at ht
            | some q => rw [hus, Option.bind_some] at ht; exact ⟨true, q, ht⟩
        obtain ⟨l, p, hlp⟩ := hdh
        have hd := decodeHead_encodeItem hlp s'
        have hsz : (Head.mk l (e.length - p.length) p.length).size = e.length := by
          have := (encodeItem_suffix hlp).1
          simp [Head.size]; omega
        cases hcase : e ++ s' with
        | nil => exact absurd (List.append_eq_nil_iff.mp hcase).1 hne
        | cons b bs =>
          rw [hcase] at hd
          simp only [List.length_append] at hn
          simp only [decodeListF, hd]
          rw [← hcase, hsz, List.take_left' rfl, List.drop_left' rfl,
            decodeTreeF_encodeTree t ht (by omega), decodeListF_encodeTrees ts hts (by
              have := List.length_pos_iff.mpr hne; omega)]
end

/-- Decoding an encoding gives the structure back (decode ∘ encode is the identity). -/
theorem decodeTree_encodeTree {t : Tree} {e : Bytes} (h : encodeTree t = some e) :
    decodeTree e = some t :=
  decodeTreeF_encodeTree t h (by omega)

theorem encode_decodeF : ∀ (n : Nat),
    (∀ w t, decodeTreeF n w = some t → encodeTree t = some w) ∧
    (∀ w ts, decodeListF n w = some ts → encodeTrees ts = some w)
  | 0 => ⟨fun _ _ h => by simp [decodeTreeF] at h, fun _ _ h => by simp [decodeListF] at h⟩
  | n + 1 => by
    obtain ⟨ihT, ihL⟩ := encode_decodeF n
    refine ⟨fun w t h => ?_, fun w ts h => ?_⟩
    · simp only [decodeTreeF] at h
      cases hd : decodeHead w with
      | none => simp [hd] at h
      | some hh =>
        rw [hd] at h
        simp only at h
        split at h
        · rename_i hsz
          have he := encodeItem_decodeHead hd
          rw [hsz, List.take_length] at he
          split at h
          · rename_i hl
            cases hts : decodeListF n (payload w hh) with
            | none => simp [hts] at h
            | some ts =>
              rw [hts] at h
              cases h
              simp only [encodeTree, ihL _ _ hts, Option.bind_some]
              simpa [encodeItem, hl] using he
          · rename_i hl
            cases h
            simpa [encodeTree, encodeItem, hl] using he
        · contradiction
    · match w, h with
      | [], h => simp only [decodeListF, Option.some.injEq] at h; subst h; rfl
      | b :: bs, h =>
        simp only [decodeListF] at h
        cases hd : decodeHead (b :: bs) with
        | none => simp [hd] at h
        | some hh =>
          rw [hd] at h
          simp only at h
          split at h
          · rename_i t ts' ht hts
            cases h
            rw [encodeTrees_cons (ihT _ _ ht) (ihL _ _ hts), List.take_append_drop]
          · contradiction

/-- What decodes is the canonical encoding of the structure decoded (encode ∘ decode is the
identity on accepted input). -/
theorem encodeTree_decodeTree {w : Bytes} {t : Tree} (h : decodeTree w = some t) :
    encodeTree t = some w :=
  (encode_decodeF _).1 w t h

end LeanLight.Spec.RlpDecode
