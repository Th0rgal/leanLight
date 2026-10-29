import LeanLightProofs.Sha256
import LeanLightProofs.Vendor.SszSpecs.Ssz.Proofs.Merkle.Authentication

/-!
# SSZ branches: what binding means, and the collision it computes

`NormalizedBranch` is consensus-specs' `is_valid_normalized_merkle_branch`
(v1.7.0-beta.4, `altair/light-client/sync-protocol.md:332-343`) over ssz-specs' verifier
`verifyMerkleProof` (vendored): the branch's leading extra roots are zero nodes, and the rest is a
branch ssz-specs accepts, every node 32 bytes wide, at the gindex, under the root.

**Binding** (`normalized_binding`): two different leaves accepted at one gindex under one root,
by normalized branches, give two different 64-byte messages with the same SHA-256 (FIPS 180-4,
`Spec.Sha256.sha256`), and `collision` computes them: a search over the pairs of messages the two
branches hash (ssz-specs' `branchMessages`), as `Spec.Mpt.collision` computes a Keccak collision
for two trie proofs. It rests on ssz-specs' `verifyMerkleProof_binding`, which assumes nothing of
SHA-256 but its 32-byte output, and on `Lc.Sha256.hash_eq_spec`; no axiom beyond Lean's.
-/

namespace LeanLight.Spec.Ssz

open _root_.Ssz (Bytes branchMessages verifyMerkleProof zeroChunk)

/-- A SHA-256 collision: two different 64-byte messages (two node pairs) with the same
SHA-256, `Spec.Sha256.sha256`. -/
def IsCollision (p : Bytes × Bytes) : Prop :=
  p.1 ≠ p.2 ∧ p.1.size = 64 ∧ p.2.size = 64 ∧
    Spec.Sha256.sha256 ⟨p.1⟩ = Spec.Sha256.sha256 ⟨p.2⟩

/-- `IsCollision`, decided. -/
def collides (p : Bytes × Bytes) : Bool :=
  p.1 != p.2 && p.1.size == 64 && p.2.size == 64 &&
    (Spec.Sha256.sha256 ⟨p.1⟩).data == (Spec.Sha256.sha256 ⟨p.2⟩).data

theorem collides_iff (p : Bytes × Bytes) : collides p = true ↔ IsCollision p := by
  simp only [collides, IsCollision, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩
    exact ⟨h₁, h₂, h₃, ByteArray.ext h₄⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨⟨⟨h₁, h₂⟩, h₃⟩, congrArg ByteArray.data h₄⟩

/-- The pair `normalized_binding` says collide, for two branches climbing from `leaf₁` and `leaf₂`
at `gindex`: the first pair of messages they hash, one from each, that is a collision; `(#[], #[])`
if there is none, which binding rules out for two accepted branches with different leaves. -/
def collision (gindex : Nat) (leaf₁ : Bytes) (branch₁ : List Bytes) (leaf₂ : Bytes)
    (branch₂ : List Bytes) : Bytes × Bytes :=
  (((branchMessages gindex 0 leaf₁ branch₁).flatMap fun a =>
      (branchMessages gindex 0 leaf₂ branch₂).map fun b => (a, b)).find? collides).getD (#[], #[])

/-- The roots of a normalized branch that `verifyMerkleProof` checks: all but the leading extra
ones. -/
def suffix (branch : List Bytes) (gindex : Nat) : List Bytes :=
  branch.drop (branch.length - gindex.log2)

/-- consensus-specs' `is_valid_normalized_merkle_branch`, over ssz-specs' verifier: the branch is
at least as long as the gindex is deep, its leading extra roots are zero nodes, and the rest
(`suffix`) is a branch ssz-specs accepts for `leaf` at `gindex` under `root`. -/
def NormalizedBranch (leaf : Bytes) (branch : List Bytes) (gindex : Nat) (root : Bytes) : Prop :=
  gindex.log2 ≤ branch.length ∧
    (∀ node ∈ branch.take (branch.length - gindex.log2), node = zeroChunk) ∧
    verifyMerkleProof leaf (suffix branch gindex) gindex root = .ok true

theorem collision_isCollision {gindex : Nat} {leaf₁ leaf₂ : Bytes} {branch₁ branch₂ : List Bytes}
    (h : ∃ a ∈ branchMessages gindex 0 leaf₁ branch₁, ∃ b ∈ branchMessages gindex 0 leaf₂ branch₂,
      IsCollision (a, b)) :
    IsCollision (collision gindex leaf₁ branch₁ leaf₂ branch₂) := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  unfold collision
  have hmem : (a, b) ∈ (branchMessages gindex 0 leaf₁ branch₁).flatMap fun a =>
      (branchMessages gindex 0 leaf₂ branch₂).map fun b => (a, b) :=
    List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨b, hb, rfl⟩⟩
  cases hf : List.find? collides _ with
  | none =>
    exact absurd ((collides_iff _).mpr hab) (by
      have := List.find?_eq_none.mp hf (a, b) hmem
      simpa using this)
  | some p =>
    exact (collides_iff p).mp (List.find?_some hf)

/-- **Binding.** Two different leaves accepted at one gindex under one root, each by a
normalized branch (`NormalizedBranch`, consensus-specs' `is_valid_normalized_merkle_branch` over
ssz-specs' verifier), give a SHA-256 collision of two 64-byte messages hashed along the two
branches, and `collision` computes it. Nothing is assumed of SHA-256. -/
theorem normalized_binding {leaf₁ leaf₂ root : Bytes} {branch₁ branch₂ : List Bytes} {gindex : Nat}
    (h₁ : NormalizedBranch leaf₁ branch₁ gindex root)
    (h₂ : NormalizedBranch leaf₂ branch₂ gindex root) (hne : leaf₁ ≠ leaf₂) :
    IsCollision (collision gindex leaf₁ (suffix branch₁ gindex) leaf₂ (suffix branch₂ gindex)) := by
  rcases _root_.Ssz.verifyMerkleProof_binding h₁.2.2 h₂.2.2 with same | ⟨a, ha, b, hb, sa, sb, ne, eq⟩
  · exact absurd same hne
  · apply collision_isCollision
    refine ⟨a, ha, b, hb, ne, sa, sb, ?_⟩
    rw [← Lc.Sha256.hash_eq_spec, ← Lc.Sha256.hash_eq_spec]
    exact eq

end LeanLight.Spec.Ssz
