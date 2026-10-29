import LeanLightProofs.SszRoot

/-!
# What the light client's decoders return fits its type

Every value an `LeanLight.Ssz` decoder returns fits its container's type (`decode_fits` for each):
integers below 2⁶⁴ (2²⁵⁶ for `base_fee_per_gas`), roots of 32 bytes, 512 keys of 48 bytes,
branches of the type's length, at most 32 bytes of `extra_data`. So `LeanLightProofs.SszRoot`'s
theorems apply to it: its `root` is ssz-specs' `hashTreeRoot` of the value it denotes.

That a decoder accepts exactly what ssz-specs' `deserialize` accepts at the container's `Desc`,
and returns the value `deserialize` does, is not proved in LC3: it is checked by the
consensus-specs vectors and their mutations (`LcTest`).
-/

namespace LeanLight.Lc.Ssz

open LeanLight.Lc.Bytes (byteAt)
open _root_.Ssz (hashTreeRoot)

theorem readLE_lt (bs : ByteArray) (off w : Nat) : readLE bs off w < 2 ^ (8 * w) := by
  induction w generalizing off with
  | zero => simp [readLE]
  | succ w ih =>
    have h1 := ih (off + 1)
    have h2 := (byteAt bs off).toNat_lt
    rw [readLE, show 8 * (w + 1) = 8 * w + 8 by omega, Nat.pow_add,
      show (2 : Nat) ^ 8 = 256 from rfl]
    generalize 2 ^ (8 * w) = X at h1 ⊢
    generalize readLE bs (off + 1) w = r at h1 ⊢
    generalize (byteAt bs off).toNat = b at h2 ⊢
    have : 2 ^ 8 = 256 := rfl
    omega

theorem u64_lt (bs : ByteArray) (off : Nat) : u64 bs off < 2 ^ 64 := readLE_lt bs off 8

theorem slice_size (bs : ByteArray) (off n : Nat) (h : off + n ≤ bs.size) :
    (slice bs off n).size = n := by
  simp [slice, Bytes.extract]; omega

theorem fields_size (bs : ByteArray) (off w k : Nat) : (fields bs off w k).size = k := by
  simp [fields]

theorem fields_mem (bs : ByteArray) (off w k : Nat) (h : off + w * k ≤ bs.size) :
    ∀ x ∈ fields bs off w k, x.size = w := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hx
  simp only [fields, Array.getElem_ofFn]
  apply slice_size
  have : i < k := by simpa [fields] using hi
  have : w * (i + 1) ≤ w * k := Nat.mul_le_mul_left _ this
  rw [Nat.mul_succ] at this
  omega

theorem roots_fits (bs : ByteArray) (off k : Nat) (h : off + 32 * k ≤ bs.size) :
    BranchFits (roots bs off k) k :=
  ⟨fields_size _ _ _ _, fields_mem _ _ _ _ h⟩

theorem BeaconBlockHeader.read_fits (bs : ByteArray) (h : 112 ≤ bs.size) : (read bs).Fits :=
  ⟨u64_lt _ _, u64_lt _ _, slice_size _ _ _ (by omega), slice_size _ _ _ (by omega),
    slice_size _ _ _ (by omega)⟩

theorem BeaconBlockHeader.decode_fits {bs : ByteArray} {h : BeaconBlockHeader}
    (hd : decode bs = some h) : h.Fits := by
  unfold decode at hd
  split at hd
  · rename_i hs; cases hd; exact read_fits bs (by rw [hs]; decide)
  · cases hd

theorem SyncCommittee.read_fits (bs : ByteArray) (h : 24624 ≤ bs.size) : (read bs).Fits := by
  have hp : (read bs).pubkeys = fields bs 0 48 syncCommitteeSize := by simp only [read]
  have ha : (read bs).aggregatePubkey = slice bs (48 * syncCommitteeSize) 48 := by simp only [read]
  refine ⟨?_, ?_, ?_⟩
  · rw [hp]; exact fields_size _ _ _ _
  · rw [hp]; exact fields_mem bs 0 48 syncCommitteeSize (by show 0 + 48 * 512 ≤ bs.size; omega)
  · rw [ha]; exact slice_size bs (48 * syncCommitteeSize) 48 (by show 48 * 512 + 48 ≤ bs.size; omega)

theorem SyncCommittee.decode_fits {bs : ByteArray} {c : SyncCommittee}
    (hd : decode bs = some c) : c.Fits := by
  unfold decode at hd
  by_cases hs : bs.size = size
  · rw [ite_eq_left hs] at hd
    rw [← Option.some.inj hd]
    exact read_fits bs (by rw [hs]; show 24624 ≤ 48 * 512 + 48; omega)
  · rw [ite_eq_right hs] at hd; exact absurd hd (by simp)

theorem SyncAggregate.read_fits (bs : ByteArray) (h : 160 ≤ bs.size) : (read bs).Fits where
  bits := slice_size bs 0 (syncCommitteeSize / 8) (by show 0 + 512 / 8 ≤ bs.size; omega)
  signature := slice_size bs (syncCommitteeSize / 8) 96 (by show 512 / 8 + 96 ≤ bs.size; omega)

theorem SyncAggregate.decode_fits {bs : ByteArray} {a : SyncAggregate}
    (hd : decode bs = some a) : a.Fits := by
  unfold decode at hd
  split at hd
  · rename_i hs; cases hd; exact read_fits bs (by rw [hs]; decide)
  · cases hd

theorem extract_size (bs : ByteArray) (a b : Nat) (h : a ≤ b) (hb : b ≤ bs.size) :
    (Bytes.extract bs a b).size = b - a := by
  simp [Bytes.extract]; omega

theorem ExecutionPayloadHeader.decode_fits {bs : ByteArray} {e : ExecutionPayloadHeader}
    (hd : decode bs = some e) : e.Fits := by
  unfold decode at hd
  split at hd
  · rename_i hc
    have h₁ : 584 ≤ bs.size := hc.1
    have h₂ : bs.size ≤ 616 := hc.2.1
    cases hd
    exact ⟨slice_size _ _ _ (by omega), slice_size _ _ _ (by omega), slice_size _ _ _ (by omega),
      slice_size _ _ _ (by omega), slice_size _ _ _ (by omega), slice_size _ _ _ (by omega),
      u64_lt _ _, u64_lt _ _, u64_lt _ _, u64_lt _ _,
      by rw [extract_size _ _ _ (by show 584 ≤ bs.size; omega) (Nat.le_refl _)]
         show bs.size - 584 ≤ 32; omega,
      readLE_lt _ _ 32, slice_size _ _ _ (by omega), slice_size _ _ _ (by omega),
      slice_size _ _ _ (by omega), u64_lt _ _, u64_lt _ _⟩
  · cases hd

theorem Electra.Header.decode_fits {bs : ByteArray} {h : Electra.Header}
    (hd : decode bs = some h) : h.Fits := by
  unfold decode at hd
  by_cases hc : fixedSize ≤ bs.size ∧ offsetAt bs 112 = fixedSize
  · rw [ite_eq_left hc] at hd
    have hs : 244 ≤ bs.size := hc.1
    cases he : ExecutionPayloadHeader.decode (Bytes.extract bs fixedSize bs.size) with
    | none => rw [he] at hd; exact absurd hd (by simp)
    | some e =>
      rw [he] at hd
      rw [← Option.some.inj hd]
      refine ⟨BeaconBlockHeader.read_fits _ ?_, ExecutionPayloadHeader.decode_fits he, ?_⟩
      · rw [slice_size bs 0 112 (by omega)]; exact Nat.le_refl _
      · exact roots_fits bs 116 executionBranchLength (by show 116 + 32 * 4 ≤ bs.size; omega)
  · rw [ite_eq_right hc] at hd; exact absurd hd (by simp)

theorem Electra.Bootstrap.decode_fits {bs : ByteArray} {b : Electra.Bootstrap}
    (hd : decode bs = some b) : b.Fits := by
  unfold decode at hd
  by_cases hc : fixedSize ≤ bs.size ∧ offsetAt bs 0 = fixedSize
  · rw [ite_eq_left hc] at hd
    have hs : 24820 ≤ bs.size := hc.1
    cases he : Header.decode (Bytes.extract bs fixedSize bs.size) with
    | none => rw [he] at hd; exact absurd hd (by simp)
    | some h =>
      rw [he] at hd
      rw [← Option.some.inj hd]
      refine ⟨Header.decode_fits he, SyncCommittee.read_fits _ ?_, ?_⟩
      · rw [slice_size _ _ _ (by show 4 + (48 * 512 + 48) ≤ bs.size; omega)]; decide
      · exact roots_fits _ _ _ (by show 4 + (48 * 512 + 48) + 32 * 6 ≤ bs.size; omega)
  · rw [ite_eq_right hc] at hd; exact absurd hd (by simp)

theorem Electra.Update.decode_fits {bs : ByteArray} {u : Electra.Update}
    (hd : decode bs = some u) : u.Fits := by
  unfold decode at hd
  simp only at hd
  by_cases hc : fixedSize ≤ bs.size ∧ offsetAt bs 0 = fixedSize ∧
      fixedSize ≤ offsetAt bs finalizedOffsetAt ∧ offsetAt bs finalizedOffsetAt ≤ bs.size
  · rw [ite_eq_left hc] at hd
    have hs : 25216 ≤ bs.size := hc.1
    cases ha : Header.decode (Bytes.extract bs fixedSize (offsetAt bs finalizedOffsetAt)) with
    | none => rw [ha] at hd; exact absurd hd (by simp)
    | some a =>
      cases hf : Header.decode (Bytes.extract bs (offsetAt bs finalizedOffsetAt) bs.size) with
      | none => rw [ha, hf] at hd; exact absurd hd (by simp)
      | some f =>
        rw [ha, hf] at hd
        rw [← Option.some.inj hd]
        refine ⟨Header.decode_fits ha, SyncCommittee.read_fits _ ?_, ?_, Header.decode_fits hf,
          ?_, SyncAggregate.read_fits _ ?_, u64_lt _ _⟩
        · rw [slice_size _ _ _ (by show 4 + (48 * 512 + 48) ≤ bs.size; omega)]; decide
        · exact roots_fits _ _ _ (by show 4 + (48 * 512 + 48) + 32 * 6 ≤ bs.size; omega)
        · exact roots_fits _ _ _ (by
            show 4 + (48 * 512 + 48) + 32 * 6 + 4 + 32 * 7 ≤ bs.size; omega)
        · rw [slice_size _ _ _ (by
            show 4 + (48 * 512 + 48) + 32 * 6 + 4 + 32 * 7 + (512 / 8 + 96) ≤ bs.size; omega)]
          decide
  · rw [ite_eq_right hc] at hd; exact absurd hd (by simp)

theorem Electra.FinalityUpdate.decode_fits {bs : ByteArray} {u : Electra.FinalityUpdate}
    (hd : decode bs = some u) : u.Fits := by
  unfold decode at hd
  simp only at hd
  by_cases hc : fixedSize ≤ bs.size ∧ offsetAt bs 0 = fixedSize ∧
      fixedSize ≤ offsetAt bs 4 ∧ offsetAt bs 4 ≤ bs.size
  · rw [ite_eq_left hc] at hd
    have hs : 400 ≤ bs.size := hc.1
    cases ha : Header.decode (Bytes.extract bs fixedSize (offsetAt bs 4)) with
    | none => rw [ha] at hd; exact absurd hd (by simp)
    | some a =>
      cases hf : Header.decode (Bytes.extract bs (offsetAt bs 4) bs.size) with
      | none => rw [ha, hf] at hd; exact absurd hd (by simp)
      | some f =>
        rw [ha, hf] at hd
        rw [← Option.some.inj hd]
        refine ⟨Header.decode_fits ha, Header.decode_fits hf, ?_, SyncAggregate.read_fits _ ?_,
          u64_lt _ _⟩
        · exact roots_fits _ _ _ (by show 8 + 32 * 7 ≤ bs.size; omega)
        · rw [slice_size _ _ _ (by show 8 + 32 * 7 + (512 / 8 + 96) ≤ bs.size; omega)]; decide
  · rw [ite_eq_right hc] at hd; exact absurd hd (by simp)

theorem Electra.OptimisticUpdate.decode_fits {bs : ByteArray} {u : Electra.OptimisticUpdate}
    (hd : decode bs = some u) : u.Fits := by
  unfold decode at hd
  by_cases hc : fixedSize ≤ bs.size ∧ offsetAt bs 0 = fixedSize
  · rw [ite_eq_left hc] at hd
    have hs : 172 ≤ bs.size := hc.1
    cases ha : Header.decode (Bytes.extract bs fixedSize bs.size) with
    | none => rw [ha] at hd; exact absurd hd (by simp)
    | some a =>
      rw [ha] at hd
      rw [← Option.some.inj hd]
      refine ⟨Header.decode_fits ha, SyncAggregate.read_fits _ ?_, u64_lt _ _⟩
      rw [slice_size _ _ _ (by show 4 + (512 / 8 + 96) ≤ bs.size; omega)]; decide
  · rw [ite_eq_right hc] at hd; exact absurd hd (by simp)

theorem Gloas.Header.read_fits (bs : ByteArray) (h : 496 ≤ bs.size) : (read bs).Fits := by
  refine ⟨BeaconBlockHeader.read_fits _ ?_, ?_, ?_⟩
  · rw [slice_size _ _ _ (by show 0 + 112 ≤ bs.size; omega)]; decide
  · exact slice_size _ _ _ (by show 112 + 32 ≤ bs.size; omega)
  · exact roots_fits _ _ _ (by show 112 + 32 + 32 * 11 ≤ bs.size; omega)

theorem Gloas.Header.decode_fits {bs : ByteArray} {h : Gloas.Header}
    (hd : decode bs = some h) : h.Fits := by
  unfold decode at hd
  by_cases hs : bs.size = size
  · rw [ite_eq_left hs] at hd
    rw [← Option.some.inj hd]
    exact read_fits bs (by rw [hs]; decide)
  · rw [ite_eq_right hs] at hd; exact absurd hd (by simp)

theorem Gloas.Bootstrap.decode_fits {bs : ByteArray} {b : Gloas.Bootstrap}
    (hd : decode bs = some b) : b.Fits := by
  unfold decode at hd
  by_cases hs : bs.size = size
  · rw [ite_eq_left hs] at hd
    have hz : bs.size = 25472 := hs
    rw [← Option.some.inj hd]
    refine ⟨Header.read_fits _ ?_, SyncCommittee.read_fits _ ?_, ?_⟩
    · rw [slice_size _ _ _ (by show 0 + 496 ≤ bs.size; omega)]; decide
    · rw [slice_size _ _ _ (by show 496 + (48 * 512 + 48) ≤ bs.size; omega)]; decide
    · exact roots_fits _ _ _ (by show 496 + (48 * 512 + 48) + 32 * 11 ≤ bs.size; omega)
  · rw [ite_eq_right hs] at hd; exact absurd hd (by simp)

theorem Gloas.Update.decode_fits {bs : ByteArray} {u : Gloas.Update}
    (hd : decode bs = some u) : u.Fits := by
  unfold decode at hd
  by_cases hs : bs.size = size
  · rw [ite_eq_left hs] at hd
    have hz : bs.size = 26424 := hs
    rw [← Option.some.inj hd]
    refine ⟨Header.read_fits _ ?_, SyncCommittee.read_fits _ ?_, ?_, Header.read_fits _ ?_, ?_,
      SyncAggregate.read_fits _ ?_, u64_lt _ _⟩
    · rw [slice_size _ _ _ (by show 0 + 496 ≤ bs.size; omega)]; decide
    · rw [slice_size _ _ _ (by show 496 + (48 * 512 + 48) ≤ bs.size; omega)]; decide
    · exact roots_fits _ _ _ (by show 496 + (48 * 512 + 48) + 32 * 11 ≤ bs.size; omega)
    · rw [slice_size _ _ _ (by show 25472 + 496 ≤ bs.size; omega)]; decide
    · exact roots_fits _ _ _ (by show 25472 + 496 + 32 * 9 ≤ bs.size; omega)
    · rw [slice_size _ _ _ (by show 26256 + (512 / 8 + 96) ≤ bs.size; omega)]; decide
  · rw [ite_eq_right hs] at hd; exact absurd hd (by simp)

theorem Gloas.FinalityUpdate.decode_fits {bs : ByteArray} {u : Gloas.FinalityUpdate}
    (hd : decode bs = some u) : u.Fits := by
  unfold decode at hd
  by_cases hs : bs.size = size
  · rw [ite_eq_left hs] at hd
    have hz : bs.size = 1448 := hs
    rw [← Option.some.inj hd]
    refine ⟨Header.read_fits _ ?_, Header.read_fits _ ?_, ?_, SyncAggregate.read_fits _ ?_,
      u64_lt _ _⟩
    · rw [slice_size _ _ _ (by show 0 + 496 ≤ bs.size; omega)]; decide
    · rw [slice_size _ _ _ (by show 496 + 496 ≤ bs.size; omega)]; decide
    · exact roots_fits _ _ _ (by show 2 * 496 + 32 * 9 ≤ bs.size; omega)
    · rw [slice_size _ _ _ (by show 1280 + (512 / 8 + 96) ≤ bs.size; omega)]; decide
  · rw [ite_eq_right hs] at hd; exact absurd hd (by simp)

theorem Gloas.OptimisticUpdate.decode_fits {bs : ByteArray} {u : Gloas.OptimisticUpdate}
    (hd : decode bs = some u) : u.Fits := by
  unfold decode at hd
  by_cases hs : bs.size = size
  · rw [ite_eq_left hs] at hd
    have hz : bs.size = 664 := hs
    rw [← Option.some.inj hd]
    refine ⟨Header.read_fits _ ?_, SyncAggregate.read_fits _ ?_, u64_lt _ _⟩
    · rw [slice_size _ _ _ (by show 0 + 496 ≤ bs.size; omega)]; decide
    · rw [slice_size _ _ _ (by show 496 + (512 / 8 + 96) ≤ bs.size; omega)]; decide
  · rw [ite_eq_right hs] at hd; exact absurd hd (by simp)

/-! ## Decoded, then hashed -/

/-- The root of an Electra (or Fulu) `LightClientHeader` decoded from any bytes is ssz-specs'
`hashTreeRoot` of the value it denotes. -/
theorem Electra.Header.decode_root {bs : ByteArray} {h : Electra.Header}
    (hd : decode bs = some h) : hashTreeRoot electraHeaderDesc h.toValue = .ok h.root.data :=
  root_eq h (decode_fits hd)

/-- Likewise for an Electra `LightClientBootstrap`. -/
theorem Electra.Bootstrap.decode_root {bs : ByteArray} {b : Electra.Bootstrap}
    (hd : decode bs = some b) : hashTreeRoot electraBootstrapDesc b.toValue = .ok b.root.data :=
  root_eq b (decode_fits hd)

/-- Likewise for an Electra `LightClientUpdate`. -/
theorem Electra.Update.decode_root {bs : ByteArray} {u : Electra.Update}
    (hd : decode bs = some u) : hashTreeRoot electraUpdateDesc u.toValue = .ok u.root.data :=
  root_eq u (decode_fits hd)

/-- Likewise for an Electra `LightClientFinalityUpdate`. -/
theorem Electra.FinalityUpdate.decode_root {bs : ByteArray} {u : Electra.FinalityUpdate}
    (hd : decode bs = some u) :
    hashTreeRoot electraFinalityUpdateDesc u.toValue = .ok u.root.data :=
  root_eq u (decode_fits hd)

/-- Likewise for an Electra `LightClientOptimisticUpdate`. -/
theorem Electra.OptimisticUpdate.decode_root {bs : ByteArray} {u : Electra.OptimisticUpdate}
    (hd : decode bs = some u) :
    hashTreeRoot electraOptimisticUpdateDesc u.toValue = .ok u.root.data :=
  root_eq u (decode_fits hd)

/-- Likewise for a Gloas `LightClientHeader`. -/
theorem Gloas.Header.decode_root {bs : ByteArray} {h : Gloas.Header}
    (hd : decode bs = some h) : hashTreeRoot gloasHeaderDesc h.toValue = .ok h.root.data :=
  root_eq h (decode_fits hd)

/-- Likewise for a Gloas `LightClientBootstrap`. -/
theorem Gloas.Bootstrap.decode_root {bs : ByteArray} {b : Gloas.Bootstrap}
    (hd : decode bs = some b) : hashTreeRoot gloasBootstrapDesc b.toValue = .ok b.root.data :=
  root_eq b (decode_fits hd)

/-- Likewise for a Gloas `LightClientUpdate`. -/
theorem Gloas.Update.decode_root {bs : ByteArray} {u : Gloas.Update}
    (hd : decode bs = some u) : hashTreeRoot gloasUpdateDesc u.toValue = .ok u.root.data :=
  root_eq u (decode_fits hd)

/-- Likewise for a Gloas `LightClientFinalityUpdate`. -/
theorem Gloas.FinalityUpdate.decode_root {bs : ByteArray} {u : Gloas.FinalityUpdate}
    (hd : decode bs = some u) : hashTreeRoot gloasFinalityUpdateDesc u.toValue = .ok u.root.data :=
  root_eq u (decode_fits hd)

/-- Likewise for a Gloas `LightClientOptimisticUpdate`. -/
theorem Gloas.OptimisticUpdate.decode_root {bs : ByteArray} {u : Gloas.OptimisticUpdate}
    (hd : decode bs = some u) :
    hashTreeRoot gloasOptimisticUpdateDesc u.toValue = .ok u.root.data :=
  root_eq u (decode_fits hd)

end LeanLight.Lc.Ssz
