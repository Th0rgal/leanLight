import LeanLight.Ssz.Merkle
import LeanLightProofs.Spec.Ssz

/-!
# The light client's normalized branches are the specification's, and binding (25b)

`LeanLight.Ssz.isValidNormalizedBranch` accepts exactly what `Spec.Ssz.NormalizedBranch` does,
consensus-specs' `is_valid_normalized_merkle_branch` over ssz-specs' `verifyMerkleProof`, on the
bytes of its arguments (`isValidNormalizedBranch_iff`). So two different leaves it accepts at one
gindex under one root give a SHA-256 collision that `Spec.Ssz.collision` computes
(`isValidNormalizedBranch_binding`).

The runtime's node hash is ssz-specs' `combine` (`hash64_data`) and its climb is `climbBranch`
(`climb_data`).
-/

namespace LeanLight.Lc.Ssz

open _root_.Ssz (Bytes combine climbBranch verifyMerkleProof calculateMerkleRoot gindexLength
  gindexDepth checkChunk checkChunks)

/-- The bytes of a branch, as the specification takes it. -/
def branchBytes (branch : Array ByteArray) : List Bytes := branch.toList.map (·.data)

theorem hash64_data (a b : ByteArray) : (hash64 a b).data = combine a.data b.data := by
  simp only [hash64, combine]
  congr 2
  exact ByteArray.ext ByteArray.data_append

theorem climb_data (g : Nat) (b : Array ByteArray) (s : Nat) :
    ∀ (n l : Nat) (node : ByteArray), (climb g b s n l node).data =
      climbBranch g l node.data ((List.range' l n).map fun k => (b[s + k]?.getD zeroChunk).data)
  | 0, _, _ => by simp [climb, climbBranch]
  | n + 1, l, node => by
    rw [climb, climb_data g b s n (l + 1), List.range'_succ, List.map_cons, climbBranch]
    congr 1
    simp only [_root_.Ssz.gindexBit]
    split <;> rename_i hb <;> simp [hash64_data, hb]

/-- The siblings `climb` reads, from `extra` on, are the branch's last `n`. -/
theorem siblings_eq (b : Array ByteArray) (extra n : Nat) (h : extra + n = b.size) :
    (List.range' 0 n).map (fun k => (b[extra + k]?.getD zeroChunk).data) =
      (branchBytes b).drop extra := by
  apply List.ext_getElem
  · simp [branchBytes]; omega
  · intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_range', branchBytes, List.getElem_drop,
      Array.getElem_toList, Nat.zero_add, Nat.one_mul]
    rw [getElem?_pos b (extra + i) (by simp at h₁; omega)]
    simp

theorem calculateMerkleRoot_ok (leaf : Bytes) (proof : List Bytes) (g : Nat) (hg : 2 ≤ g)
    (hl : proof.length = g.log2) :
    calculateMerkleRoot leaf proof g = .ok (climbBranch g 0 leaf proof) := by
  have hpos : g.log2 ≠ 0 := by
    intro h0
    have := Nat.lt_log2_self (n := g)
    rw [h0] at this
    omega
  simp [calculateMerkleRoot, gindexLength, gindexDepth, hpos, hl, show ¬g < 1 by omega,
    bind, Except.bind, pure, Except.pure]

theorem zero_node (x : ByteArray) (hs : x.size = 32)
    (hz : ∀ (j : Nat) (h : j < x.data.size), x.data[j] = 0) : x.data = _root_.Ssz.zeroChunk := by
  apply Array.ext
  · simpa [_root_.Ssz.zeroChunk] using hs
  · intro i h₁ h₂
    simp [_root_.Ssz.zeroChunk, hz i h₁]

/-- The runtime's normalized branch check accepts only what the specification's does. -/
theorem isValidNormalizedBranch_sound {leaf root : ByteArray} {branch : Array ByteArray} {g : Nat}
    (h : isValidNormalizedBranch leaf branch g root = true) :
    Spec.Ssz.NormalizedBranch leaf.data (branchBytes branch) g root.data := by
  simp only [isValidNormalizedBranch, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    Array.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hg, hd⟩, hl⟩, hall⟩, hz⟩, hc⟩ := h
  have hlen : (branchBytes branch).length = branch.size := by simp [branchBytes]
  refine ⟨by omega, ?_, ?_⟩
  · intro node hn
    rw [hlen, branchBytes, ← List.map_take, List.mem_map] at hn
    obtain ⟨x, hx, rfl⟩ := hn
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < branch.size - g.log2 := by simpa using hi
    have hzi := hz i (by simp; omega)
    simp only [Array.getElem_extract, Nat.zero_add] at hzi
    rw [List.getElem_take, Array.getElem_toList]
    exact zero_node _ (by simpa using hall i (by omega)) hzi
  · rw [_root_.Ssz.verifyMerkleProof_eq_true_iff]
    have hsuf : Spec.Ssz.suffix (branchBytes branch) g =
        (List.range' 0 g.log2).map (fun k => (branch[branch.size - g.log2 + k]?.getD zeroChunk).data) := by
      rw [Spec.Ssz.suffix, hlen, siblings_eq _ _ _ (by omega)]
    refine ⟨by simpa using hl, ?_, ?_⟩
    · intro node hn
      rw [Spec.Ssz.suffix, branchBytes, ← List.map_drop, List.mem_map] at hn
      obtain ⟨x, hx, rfl⟩ := hn
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      rw [List.getElem_drop, Array.getElem_toList]
      simpa using hall _ (by simp at hi; omega)
    · rw [calculateMerkleRoot_ok _ _ _ hg (by simp [Spec.Ssz.suffix, hlen]; omega), hsuf,
        ← climb_data, hc]

/-- The runtime's normalized branch check accepts everything the specification's does. -/
theorem isValidNormalizedBranch_complete {leaf root : ByteArray} {branch : Array ByteArray}
    {g : Nat} (h : Spec.Ssz.NormalizedBranch leaf.data (branchBytes branch) g root.data) :
    isValidNormalizedBranch leaf branch g root = true := by
  obtain ⟨hd, hz, hv⟩ := h
  obtain ⟨hl, hw, hc⟩ := (_root_.Ssz.verifyMerkleProof_eq_true_iff ..).mp hv
  have hlen : (branchBytes branch).length = branch.size := by simp [branchBytes]
  unfold calculateMerkleRoot at hc
  cases hm : gindexLength g with
  | error e => simp [hm, bind, Except.bind] at hc
  | ok depth =>
    obtain ⟨hdep, hg1, hne⟩ := _root_.Ssz.gindexLength_ok hm
    simp only [hm, bind, Except.bind] at hc
    split at hc
    · simp at hc
    · rename_i hsl
      simp only [pure, Except.pure, Except.ok.injEq] at hc
      have hg : 2 ≤ g := by
        rcases (by omega : g = 1 ∨ 2 ≤ g) with rfl | h2
        · simp at hdep; omega
        · exact h2
      have hd' : g.log2 ≤ branch.size := by omega
      simp only [isValidNormalizedBranch, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
        Array.all_eq_true]
      refine ⟨⟨⟨⟨⟨hg, hd'⟩, by simpa using hl⟩, ?_⟩, ?_⟩, ?_⟩
      · intro i hi
        by_cases hp : i < branch.size - g.log2
        · have := hz (branch[i].data) (by
            rw [hlen, branchBytes, ← List.map_take, List.mem_map]
            exact ⟨branch[i], List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩, rfl⟩)
          simpa [_root_.Ssz.zeroChunk] using congrArg Array.size this
        · have := hw (branch[i].data) (by
            rw [Spec.Ssz.suffix, hlen, branchBytes, ← List.map_drop, List.mem_map]
            exact ⟨branch[i], List.mem_iff_getElem.mpr ⟨i - (branch.size - g.log2),
              by simp; omega, by simp; congr 1; omega⟩, rfl⟩)
          simpa using this
      · intro i hi
        simp only [Array.size_extract] at hi
        have := hz ((branch.extract 0 (branch.size - g.log2))[i].data) (by
          rw [hlen, branchBytes, ← List.map_take, List.mem_map]
          exact ⟨_, List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩, rfl⟩)
        have e : ∀ (a : Array UInt8), a = _root_.Ssz.zeroChunk → ∀ (j : Nat) (hj : j < a.size),
            a[j] = 0 := by
          intro a ha j hj; subst ha; simp [_root_.Ssz.zeroChunk]
        intro j hj
        exact e _ this j hj
      · have hsuf : Spec.Ssz.suffix (branchBytes branch) g = (List.range' 0 g.log2).map
            (fun k => (branch[branch.size - g.log2 + k]?.getD zeroChunk).data) := by
          rw [Spec.Ssz.suffix, hlen, siblings_eq _ _ _ (by omega)]
        rw [climb_data, ← hsuf]
        exact hc

/-- The runtime's normalized branch check is the specification's, on the bytes. -/
theorem isValidNormalizedBranch_iff {leaf root : ByteArray} {branch : Array ByteArray} {g : Nat} :
    isValidNormalizedBranch leaf branch g root = true ↔
      Spec.Ssz.NormalizedBranch leaf.data (branchBytes branch) g root.data :=
  ⟨isValidNormalizedBranch_sound, isValidNormalizedBranch_complete⟩

/-- **Binding**, for the code that runs: two different leaves `isValidNormalizedBranch` accepts at
one gindex under one root give a SHA-256 collision that `Spec.Ssz.collision` computes from the
two branches. -/
theorem isValidNormalizedBranch_binding {leaf₁ leaf₂ root : ByteArray}
    {branch₁ branch₂ : Array ByteArray} {g : Nat}
    (h₁ : isValidNormalizedBranch leaf₁ branch₁ g root = true)
    (h₂ : isValidNormalizedBranch leaf₂ branch₂ g root = true) (hne : leaf₁ ≠ leaf₂) :
    Spec.Ssz.IsCollision (Spec.Ssz.collision g leaf₁.data (Spec.Ssz.suffix (branchBytes branch₁) g)
      leaf₂.data (Spec.Ssz.suffix (branchBytes branch₂) g)) :=
  Spec.Ssz.normalized_binding (isValidNormalizedBranch_sound h₁) (isValidNormalizedBranch_sound h₂)
    (fun h => hne (ByteArray.ext h))

end LeanLight.Lc.Ssz
