import LeanLight.Base.Sha256
import LeanLightProofs.Spec.Sha256Folds
import LeanLightProofs.Vendor.SszSpecs.Ssz.Proofs.Hash.Sha256Laws

/-!
# The light client's SHA-256 is the specification's

`LeanLight.Base.Sha256`, ssz-specs' SHA-256 vendored as runtime code (namespace `Ssz.Sha256`), computes
`Spec.Sha256.sha256`, VCVio's FIPS 180-4 transcription, on every message, of any length:
`hash_eq_spec`. The `csimp` equations of `LeanLight.Base.Sha256` replace its definitions by faster
ones in the code that runs; this theorem is about the definitions, so it covers the code that
runs through them.

The proof is direct, block by block, over the restatements in `Spec.Sha256Folds`:

* the padding is the same bytes (`pad_eq_spec`: the zero count `(64 - (n + 9) % 64) % 64` is
  `(56 + 64 - (n + 1) % 64) % 64`, and the length is the same eight big-endian bytes, both
  computing the bit count `8 n` modulo 2⁶⁴);
* the schedule words are the same (`schedule_eq_spec`, by strong induction from ssz-specs'
  `schedule_input` and `schedule_recurrence` and the specification's `schedW_lt` and
  `schedW_ge`); the round constants and the initial state are the same literals;
* one round is the same eight-word step (`toVars_round`), so one compression is
  (`compress_eq_spec`), and so is the chain over the blocks (`blocks_eq_spec`);
* the digest writes the same 32 bytes (`digest_eq_spec`).
-/

namespace LeanLight.Lc.Sha256

open LeanLight.Refinement.Sha256 (schedW beWord expandAt schedW_lt schedW_ge rounds roundStep addVars
  Vars compress_eq pad_eq sha256_eq padZeros)
open SLHDSA.Concrete.Sha2 (k iv u32be u64be stateBytes32 rotr ch maj bsig0 bsig1 ssig0 ssig1)

/-! ## Words and constants -/

theorem getElem!_eq_getD (m : ByteArray) (i : Nat) : m[i]! = m[i]?.getD 0 := by
  by_cases h : i < m.size
  · rw [getElem!_pos m i h, getElem?_pos m i h]; rfl
  · rw [getElem!_neg m i h, getElem?_neg m i h]; rfl

/-- ssz-specs' big-endian word, read with `getD`, is the specification's, read with `!`. -/
theorem wordAt_eq (m : ByteArray) (o : Nat) : Ssz.Sha256.wordAt m o = beWord m o := by
  simp only [Ssz.Sha256.wordAt, beWord, getElem!_eq_getD]

theorem roundConstants_eq : Ssz.Sha256.roundConstants.toArray = k := rfl

theorem initialState_eq : Ssz.Sha256.initialState.toArray = iv := rfl

theorem sigma0_eq : Ssz.Sha256.sigma0 = ssig0 := rfl
theorem sigma1_eq : Ssz.Sha256.sigma1 = ssig1 := rfl
theorem bigSigma0_eq : Ssz.Sha256.bigSigma0 = bsig0 := rfl
theorem bigSigma1_eq : Ssz.Sha256.bigSigma1 = bsig1 := rfl
theorem choose_eq : Ssz.Sha256.choose = ch := rfl
theorem majority_eq : Ssz.Sha256.majority = maj := rfl

/-! ## The schedule -/

/-- The four terms of the schedule recurrence, added in the other order. -/
theorem add_reverse (a b c d : UInt32) : a + b + c + d = d + c + b + a := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_add]
  omega

/-- Each of the 64 schedule words of a block is the specification's. -/
theorem schedule_eq_spec (m : ByteArray) (base i : Nat) (h : i < 64) :
    (Ssz.Sha256.schedule m base)[i] = (schedW m base)[i]! := by
  induction i using Nat.strongRecOn with
  | _ i ih =>
    by_cases hi : i < 16
    · rw [Ssz.Sha256.schedule_input m base i hi, schedW_lt m base i hi, wordAt_eq, Nat.mul_comm]
    · rw [Ssz.Sha256.schedule_recurrence m base i (by omega) h, schedW_ge m base i (by omega) h]
      simp only [expandAt]
      rw [ih (i - 16) (by omega) (by omega), ih (i - 15) (by omega) (by omega),
        ih (i - 7) (by omega) (by omega), ih (i - 2) (by omega) (by omega), sigma0_eq, sigma1_eq]
      exact add_reverse _ _ _ _

/-! ## The rounds and one compression -/

/-- The eight working variables of a state, as the specification threads them. -/
def toVars (x : Vector UInt32 8) : Vars := ⟨x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]⟩

/-- One of ssz-specs' rounds is the specification's round `t`, given the same constant and word. -/
theorem toVars_round (w : Array UInt32) (x : Vector UInt32 8) (c word : UInt32) (t : Nat)
    (hc : c = k[t]!) (hw : word = w[t]!) :
    toVars (Ssz.Sha256.round x c word) = roundStep w (toVars x) t := by
  subst hc hw
  simp only [toVars, Ssz.Sha256.round, roundStep, bigSigma1_eq, bigSigma0_eq, choose_eq,
    majority_eq]
  simp

theorem toArray_getElem! {n : Nat} (v : Vector UInt32 n) (i : Nat) (h : i < n) : v.toArray[i]! = v[i] := by
  rw [getElem!_pos v.toArray i (by simpa using h)]
  simp

theorem foldl_round (m : ByteArray) (base : Nat) (x : Vector UInt32 8) (l : List (Fin 64)) :
    toVars (l.foldl (fun current i =>
        Ssz.Sha256.round current Ssz.Sha256.roundConstants[i] (Ssz.Sha256.schedule m base)[i]) x) =
      (l.map (·.val)).foldl (fun v t => roundStep (schedW m base) v t) (toVars x) := by
  induction l generalizing x with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih, toVars_round (schedW m base) x _ _ i.val
      (by rw [← roundConstants_eq, toArray_getElem! _ _ i.isLt]; rfl)
      (by rw [← schedule_eq_spec m base i.val i.isLt]; rfl)]

theorem finRange_val : (List.finRange 64).map (·.val) = List.range' 0 64 := by
  apply List.ext_getElem <;> simp

/-- The final addition of ssz-specs' compression is the specification's `addVars`. -/
theorem zipWith_add (v w : Vector UInt32 8) :
    (v.zipWith (· + ·) w).toArray = addVars v.toArray (toVars w) := by
  apply Array.ext
  · simp [addVars]
  · intro i h₁ _
    have hi : i < 8 := by simpa using h₁
    simp only [addVars, toVars, toArray_getElem! v _ (by decide : 0 < 8),
      toArray_getElem! v _ (by decide : 1 < 8), toArray_getElem! v _ (by decide : 2 < 8),
      toArray_getElem! v _ (by decide : 3 < 8), toArray_getElem! v _ (by decide : 4 < 8),
      toArray_getElem! v _ (by decide : 5 < 8), toArray_getElem! v _ (by decide : 6 < 8),
      toArray_getElem! v _ (by decide : 7 < 8)]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- One compression of ssz-specs' is the specification's, on the same eight words. -/
theorem compress_eq_spec (v : Vector UInt32 8) (m : ByteArray) (base : Nat) :
    (Ssz.Sha256.compress v m base).toArray = SLHDSA.Concrete.Sha2.compress v.toArray m base := by
  rw [compress_eq]
  have hr : rounds v.toArray (schedW m base) =
      (List.range' 0 64).foldl (fun s t => roundStep (schedW m base) s t) (toVars v) := by
    simp only [rounds, toVars, toArray_getElem! v _ (by decide : 0 < 8),
      toArray_getElem! v _ (by decide : 1 < 8), toArray_getElem! v _ (by decide : 2 < 8),
      toArray_getElem! v _ (by decide : 3 < 8), toArray_getElem! v _ (by decide : 4 < 8),
      toArray_getElem! v _ (by decide : 5 < 8), toArray_getElem! v _ (by decide : 6 < 8),
      toArray_getElem! v _ (by decide : 7 < 8)]
  rw [hr, ← finRange_val, ← foldl_round]
  simp only [Ssz.Sha256.compress]
  exact zipWith_add _ _

/-- The chain over the blocks of a padded message is the specification's. -/
theorem blocks_eq_spec (p : ByteArray) (v : Vector UInt32 8) (l : List Nat) :
    (l.foldl (fun current block => Ssz.Sha256.compress current p (64 * block)) v).toArray =
      l.foldl (fun st b => SLHDSA.Concrete.Sha2.compress st p (b * 64)) v.toArray := by
  induction l generalizing v with
  | nil => rfl
  | cons b l ih => rw [List.foldl_cons, List.foldl_cons, ih, compress_eq_spec, Nat.mul_comm 64 b]

/-! ## Padding and the digest -/

theorem paddingZeros_eq (n : Nat) : Ssz.Sha256.paddingZeros n = padZeros n := by
  simp only [Ssz.Sha256.paddingZeros, padZeros]
  omega

theorem lengthBytes_eq (n : Nat) : Ssz.Sha256.lengthBytes n = u64be (n.toUInt64 * 8) := by
  simp only [Ssz.Sha256.lengthBytes, u64be]
  congr 1

/-- ssz-specs' padding is the specification's, on every message. -/
theorem pad_eq_spec (m : ByteArray) : Ssz.Sha256.pad m = SLHDSA.Concrete.Sha2.pad m := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [pad_eq]
  simp [Ssz.Sha256.pad, paddingZeros_eq, lengthBytes_eq]

/-- Byte `r` of a word, big-endian, as ssz-specs' digest computes it. -/
theorem u32be_byte (x : UInt32) (r : Nat) (hr : r < 4) :
    (x >>> (24 - 8 * UInt32.ofNat r)).toUInt8 = (u32be x)[r]! := by
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;>
    simp [u32be] <;> rfl

/-- ssz-specs' digest of the final state is the specification's 32 bytes. -/
theorem digest_eq_spec (v : Vector UInt32 8) :
    Ssz.Sha256.digest v = (stateBytes32 v.toArray).extract 0 32 := by
  rw [show (32 : Nat) = (stateBytes32 v.toArray).size from
    (SLHDSA.Concrete.Sha2.stateBytes32_size _).symm, ByteArray.extract_zero_size]
  apply ByteArray.ext
  apply Array.ext
  · simp [Ssz.Sha256.digest, stateBytes32]
  · intro i h₁ _
    have hi : i < 32 := by simpa [Ssz.Sha256.digest] using h₁
    simp only [Ssz.Sha256.digest, stateBytes32, Array.getElem_ofFn]
    rw [toArray_getElem! v _ (by omega)]
    exact u32be_byte _ _ (Nat.mod_lt _ (by decide))

/--
The light client's SHA-256 (`LeanLight.Base.Sha256`, ssz-specs' `Ssz.Sha256.hash`) is the
specification's, `Spec.Sha256.sha256` (FIPS 180-4, VCVio's, vendored), on every message. FIPS
180-4 defines SHA-256 below 2⁶⁴ bits; past that, both write the bit length modulo 2⁶⁴ alike, so
no size bound is needed. The runtime's `csimp` equations (`LeanLight.Base.Sha256`, audited) make
the code that runs these definitions.
-/
theorem hash_eq_spec (m : ByteArray) : Ssz.Sha256.hash m = Spec.Sha256.sha256 m := by
  rw [sha256_eq]
  simp only [Ssz.Sha256.hash]
  rw [pad_eq_spec, digest_eq_spec, blocks_eq_spec, initialState_eq]

end LeanLight.Lc.Sha256
