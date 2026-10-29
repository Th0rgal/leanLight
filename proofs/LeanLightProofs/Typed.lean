import LeanLight.El.Typed
import LeanLight.El.Trie
import LeanLightProofs.Anchor

/-!
# What a transaction's or a receipt's envelope is (LC8)

About `LeanLight.El.Typed`, the code `lkd-lc` runs:

* `items_spec`: a block's list `items` accepts is the canonical RLP list of its items' bytes,
  each nonempty;
* `txType_spec`: a transaction `txType` accepts is its type's byte (none for legacy, whose first
  byte starts a list), then one canonical RLP list of its type's number of fields;
* `receipt_spec`: a receipt `receipt` accepts is its type's byte, then one canonical RLP list
  whose first item is the status `receipt` returns: `0x01` for success, the empty string
  (`0x80`) for failure.
-/

namespace LeanLight.Lc.Typed

open LeanLight.Spec.Rlp
open LeanLight.Spec.RlpDecode
open LeanLight.Lc.Bytes (byteAt byteAt_eq size_eq)

/-- The type byte an envelope of type `t` starts with: none for a legacy one. -/
def typeBytes (t : Nat) : Bytes := if t = 0 then [] else [t.toUInt8]

theorem envelope_spec {bs : ByteArray} {a b t s : Nat} (h : envelope bs a b = some (t, s)) :
    a < b ∧ b ≤ bs.size ∧ t ≤ 4 ∧ s ≤ b ∧ window bs.data.toList a b = typeBytes t ++ window bs.data.toList s b ∧
      (t = 0 → 0xc0 ≤ (byteAt bs a).toNat) := by
  unfold envelope at h
  split at h
  · rename_i hab
    have hl : b ≤ bs.data.toList.length := by rw [size_eq]; exact hab.2
    have hw := window_cons hab.1 hl
    rw [← byteAt_eq] at hw
    simp only at h
    split at h
    · rename_i hc
      cases h
      exact ⟨hab.1, hab.2, by omega, by omega, by simp [typeBytes], fun _ => hc⟩
    · rename_i hc
      split at h
      · rename_i ht
        cases h
        refine ⟨hab.1, hab.2, ht.2, by omega, ?_, fun h0 => by omega⟩
        rw [hw, typeBytes, ite_eq_right (by omega)]
        congr 1
        have := (byteAt bs a).toNat_lt
        apply UInt8.toNat_inj.mp
        simp [Nat.toUInt8]
      · cases h
  · cases h

theorem listAt_spec {bs : ByteArray} {s b : Nat} {cs : List Span} (h : listAt bs s b = some cs) :
    s < b ∧ b ≤ bs.size ∧ ∃ top : Span, top.pos = s ∧ top.stop = b ∧
      encodeList (window bs.data.toList top.start top.stop) = some (window bs.data.toList s b) ∧
      itemsAt bs.data.toList top.start top.stop = some cs := by
  unfold listAt at h
  split at h
  · rename_i top htop
    rw [itemAtB_eq] at htop
    split at h
    · rename_i hc
      rw [itemsAtB_eq] at h
      obtain ⟨hpos, -, -, hlt, -, hb, -, henc⟩ := itemAt_span htop
      rw [hc.1, hc.2] at henc
      refine ⟨by omega, by rw [← size_eq]; exact hb, top, hpos, hc.2, ?_, h⟩
      rw [hc.2]; exact henc
    · cases h
  · cases h

/-- **A block's list.** The bytes `items` reads are the canonical RLP list of its items'
payloads, each nonempty. -/
theorem items_spec {bs : ByteArray} {its : List Span} (h : items bs = some its) :
    encodeTree (.branch ((its.map fun it => (Trie.valueOf bs it).data.toList).map .leaf)) =
      some bs.data.toList ∧
    ∀ it ∈ its, (Trie.valueOf bs it).data.toList ≠ [] := by
  unfold items at h
  cases hl : listAt bs 0 bs.size with
  | none => rw [hl] at h; cases h
  | some cs =>
    rw [hl] at h
    simp only at h
    split at h
    · rename_i hall
      cases h
      have hf : Anchor.fieldsB bs = some (its.map (Spec.Header.payloadOfB bs)) := by
        have hl' := hl
        unfold listAt at hl'
        unfold Anchor.fieldsB
        cases htop : itemAtB bs 0 bs.size with
        | none => rw [htop] at hl'; cases hl'
        | some top =>
          rw [htop] at hl'
          simp only at hl' ⊢
          split at hl'
          · rename_i hc
            rw [ite_eq_left hc, hl']
            simp only
            rw [ite_eq_left (List.all_eq_true.mpr fun it hit => by
              have := List.all_eq_true.mp hall it hit
              simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
              simp [this.1])]
          · cases hl'
      have he := Anchor.fieldsL_encode (by rw [← Anchor.fieldsB_eq]; exact hf)
      refine ⟨he, fun it hit => ?_⟩
      have hn := List.all_eq_true.mp hall it hit
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hn
      obtain ⟨-, -, top, -, -, -, hits⟩ := listAt_spec hl
      obtain ⟨hsp, -⟩ := itemsAt_spans hits
      obtain ⟨-, -, hat⟩ := hsp it hit
      obtain ⟨-, -, -, -, hst, hb, -, -⟩ := itemAt_span hat
      intro h0
      have hl0 := congrArg List.length h0
      simp only [Trie.valueOf, Bytes.extract_eq, List.length_drop, List.length_take,
        List.length_nil] at hl0
      have hsz := size_eq bs
      omega
    · cases h

/-- **A transaction's envelope.** A transaction `txType` accepts is its type's byte (none for a
legacy one, whose first byte starts a list), then one canonical RLP list, whose payload holds
its type's number of fields. -/
theorem txType_spec {bs : ByteArray} {a b t : Nat} (h : txType bs a b = some t) :
    t ≤ 4 ∧ (t = 0 → 0xc0 ≤ (byteAt bs a).toNat) ∧
      ∃ (top : Span) (fs : List Field) (cs : List Span),
        window bs.data.toList a b = typeBytes t ++ window bs.data.toList top.pos b ∧
        encodeList (window bs.data.toList top.start top.stop) = some (window bs.data.toList top.pos b) ∧
        itemsAt bs.data.toList top.start top.stop = some cs ∧ txFields t = some fs ∧
        cs.length = fs.length := by
  unfold txType at h
  split at h
  · cases h
  · rename_i t' s hen
    obtain ⟨hab, hb, ht, hsb, hw, h0⟩ := envelope_spec hen
    split at h
    · rename_i cs fs hcs hfs
      split at h
      · rename_i hok
        cases h
        obtain ⟨-, -, top, hpos, hstop, henc, hits⟩ := listAt_spec hcs
        unfold fieldsOk at hok
        simp only [Bool.and_eq_true, beq_iff_eq] at hok
        refine ⟨ht, h0, top, fs, cs, by rw [hpos]; exact hw, by rw [hpos]; exact henc, hits, hfs,
          hok.1.symm⟩
      · cases h
    · cases h

/-- **A receipt's envelope and status.** A receipt `receipt` accepts is its type's byte, then one
canonical RLP list whose first item is the status it returns: `0x01` for success, the empty
string (`0x80`) for failure (EIP-658). -/
theorem receipt_spec {bs : ByteArray} {a b t : Nat} {ok : Bool} (h : receipt bs a b = some (t, ok)) :
    t ≤ 4 ∧ (t = 0 → 0xc0 ≤ (byteAt bs a).toNat) ∧
      ∃ (top : Span) (rest : Bytes),
        window bs.data.toList a b = typeBytes t ++ window bs.data.toList top.pos b ∧
        encodeList (window bs.data.toList top.start top.stop) = some (window bs.data.toList top.pos b) ∧
        window bs.data.toList top.start top.stop = (if ok then [0x01] else [0x80]) ++ rest := by
  unfold receipt at h
  split at h
  · cases h
  · rename_i t' s hen
    obtain ⟨hab, hb, ht, hsb, hw, h0⟩ := envelope_spec hen
    split at h
    · rename_i st rest hcs
      split at h
      · rename_i ok' hst
        split at h
        · cases h
          obtain ⟨-, hbs, top, hpos, hstop, henc, hits⟩ := listAt_spec hcs
          obtain ⟨hsp, hflat⟩ := itemsAt_spans hits
          obtain ⟨-, -, hat⟩ := hsp st (by simp)
          obtain ⟨-, -, -, -, hss, hlen, -, hfound⟩ := itemAt_span hat
          have hpos0 : st.pos = top.start := by
            unfold itemsAt at hits
            split at hits
            · rename_i hle
              obtain ⟨n, hn⟩ : ∃ n, top.stop - top.start + 1 = n + 1 := ⟨_, rfl⟩
              rw [hn] at hits
              simp only [itemsF] at hits
              split at hits
              · split at hits
                · cases hits
                · rename_i it hit
                  cases hn' : itemsF n bs.data.toList it.stop top.stop with
                  | none => rw [hn'] at hits; cases hits
                  | some r =>
                    rw [hn', Option.map_some, Option.some.injEq, List.cons.injEq] at hits
                    rw [← hits.1]
                    exact (itemAt_span hit).1
              · cases hits
            · cases hits
          have hstat : window bs.data.toList st.pos st.stop = if ok then [0x01] else [0x80] := by
            unfold status at hst
            split at hst
            · cases hst
            · rename_i hl
              simp only [Bool.not_eq_true] at hl
              rw [hl] at hfound
              split at hst
              · rename_i he
                cases hst
                simp only [Bool.false_eq_true, ite_false]
                rw [he] at hfound
                have : window bs.data.toList st.stop st.stop = [] := window_empty _ (Nat.le_refl _)
                rw [this] at hfound
                simp only [encodeItem, Bool.false_eq_true, ite_false, encodeBytes] at hfound
                simpa using hfound.symm
              · split at hst
                · rename_i h1
                  cases hst
                  simp only [ite_true]
                  have hw1 : window bs.data.toList st.start st.stop = [1] := by
                    have hl1 : (window bs.data.toList st.start st.stop).length = 1 := by
                      rw [window_length (show st.stop ≤ bs.data.toList.length by omega)]; omega
                    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hl1
                    rw [hx]
                    have := window_getElem? bs.data.toList st.start st.stop 0
                    rw [hx, ite_eq_left (by omega), Nat.add_zero] at this
                    have hb1 : bs.data.toList[st.start]?.getD 0 = 1 := by
                      rw [← byteAt_eq]; exact h1.2
                    rw [← this] at hb1
                    simpa using hb1
                  rw [hw1] at hfound
                  simp only [encodeItem, Bool.false_eq_true, ite_false, encodeBytes] at hfound
                  simpa using hfound.symm
                · cases hst
          refine ⟨ht, h0, top, (rest.map fun it => window bs.data.toList it.pos it.stop).flatten,
            by rw [hpos]; exact hw, by rw [hpos]; exact henc, ?_⟩
          rw [← hflat, List.map_cons, List.flatten_cons, hstat]
        · cases h
      · cases h
    · cases h

end LeanLight.Lc.Typed
