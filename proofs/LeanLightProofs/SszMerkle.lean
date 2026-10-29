import LeanLight.Ssz.Merkle
import LeanLightProofs.SszBranch
import LeanLightProofs.Vendor.SszSpecs.Ssz.Codec.Root

/-!
# The light client's merkleization pieces are ssz-specs'

Over the bytes, each building block of `LeanLight.Ssz.Merkle` is the vendored specification's:
`leBytes` is `uintBytes`, `pack` is `packBytes`, `zeroHashes` is `zeroRoots`, `zeroHash` is
`zeroSubtree` (for depths up to 64, where the table holds them) and `subtree` is `subtreeAt`
(likewise). `LeanLightProofs.SszRoot` builds the containers' roots on these.
-/

namespace LeanLight.Lc.Ssz

open _root_.Ssz (Bytes combine)

/-- The bytes of an array of nodes, as the specification takes it. -/
def nodes (cs : Array ByteArray) : Array Bytes := cs.map (·.data)

theorem zeroChunk_data : zeroChunk.data = _root_.Ssz.zeroChunk := rfl

theorem leBytes_data (w v : Nat) : (leBytes w v).data = _root_.Ssz.uintBytes w v := by
  induction w generalizing v with
  | zero => rfl
  | succ w ih => simp [leBytes, _root_.Ssz.uintBytes, ih]

theorem zeroHashesUpTo_data (d : Nat) :
    nodes (zeroHashesUpTo d) = _root_.Ssz.zeroRootsUpTo d := by
  induction d with
  | zero => simp [nodes, zeroHashesUpTo, _root_.Ssz.zeroRootsUpTo]; rfl
  | succ d ih =>
    simp only [zeroHashesUpTo, _root_.Ssz.zeroRootsUpTo, nodes, Array.map_push] at *
    rw [ih, hash64_data]
    congr 2 <;> rw [← ih, Array.getElem?_map, Option.getD_map] <;> rfl

theorem zeroRootsUpTo_size (d : Nat) : (_root_.Ssz.zeroRootsUpTo d).size = d + 1 := by
  induction d with
  | zero => rfl
  | succ d ih => simp [_root_.Ssz.zeroRootsUpTo, ih]

theorem zeroHash_data (d : Nat) (hd : d ≤ 64) : (zeroHash d).data = _root_.Ssz.zeroSubtree d := by
  have hs : d < (_root_.Ssz.zeroRootsUpTo 64).size := by rw [zeroRootsUpTo_size]; omega
  have hm : d < (zeroHashesUpTo 64).size := by
    rw [← Array.size_map (f := (·.data)), show (zeroHashesUpTo 64).map (·.data) = nodes _ from rfl,
      zeroHashesUpTo_data]; exact hs
  rw [_root_.Ssz.zeroSubtree, _root_.Ssz.zeroRoots, show _root_.Ssz.maxZeroDepth = 64 from rfl,
    ← zeroHashesUpTo_data]
  obtain ⟨x, hx⟩ : ∃ x, (zeroHashesUpTo 64)[d]? = some x := ⟨_, Array.getElem?_eq_getElem hm⟩
  simp [zeroHash, zeroHashes, nodes, Array.getElem?_map, hx]

theorem subtree_data (chunks : Array ByteArray) :
    ∀ (d : Nat), d ≤ 64 → ∀ (start : Nat),
      (subtree chunks d start).data = _root_.Ssz.subtreeAt (nodes chunks) d start
  | d, hd, start => by
    rw [subtree.eq_def, _root_.Ssz.subtreeAt.eq_def]
    dsimp only
    have hsz : (nodes chunks).size = chunks.size := by simp [nodes]
    rw [hsz]
    by_cases hs : start ≥ chunks.size
    · rw [ite_eq_left hs, ite_eq_left hs]; exact zeroHash_data d hd
    · rw [ite_eq_right hs, ite_eq_right hs]
      match d with
      | 0 =>
        simp only [_root_.Ssz.padded, nodes, Array.getElem?_map, Option.getD_map]
        rfl
      | d + 1 =>
        simp only
        rw [hash64_data, subtree_data chunks d (by omega), subtree_data chunks d (by omega)]

theorem pack_data (data : ByteArray) : nodes (pack data) = _root_.Ssz.packBytes data.data := by
  apply Array.ext
  · simp [nodes, pack, _root_.Ssz.packBytes]
  · intro i h₁ h₂
    simp only [nodes, pack, _root_.Ssz.packBytes, Array.getElem_map, Array.getElem_ofFn,
      ByteArray.data_append]
    have he : (Bytes.extract data (i * chunkSize) (i * chunkSize + chunkSize)).data =
        data.data.extract (i * _root_.Ssz.bytesPerChunk) (i * _root_.Ssz.bytesPerChunk +
          _root_.Ssz.bytesPerChunk) := by
      apply Array.toList_inj.mp
      rw [Bytes.extract_eq, Array.toList_extract, List.extract_eq_take_drop, List.drop_take]
    rw [he, ← ByteArray.size_data, he]

end LeanLight.Lc.Ssz
