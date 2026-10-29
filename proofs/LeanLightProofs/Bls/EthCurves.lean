import LeanLightProofs.Bls.Curves
import LeanLightProofs.Vendor.EthLib.Bls.Compress

/-!
# BLS12-381: EthLib's G1 and G2 formulas are the group law too (25c)

EthLib's readable layer computes G1 and G2 in Jacobian coordinates of its own (`G1`, `G2`, over
`Fin p` and its `Fp2`): the same dbl-2009-l and add-2007-bl as the runtime, but with a
bottom-up double-and-add (`mulNat`). Read as triples of `𝔽_p` and `𝔽_{p²}` (`Eth.g1J`,
`Eth.g2J`), they are `Jac`'s (`LeanLightProofs.Bls.Jacobian`), so on nonsingular points:

* `double`, `add` and `mulNat` double, add and multiply (`Eth.G1.double_spec`, `add_spec`,
  `mulNat_spec`, and G2's), the identity `zero` included (`Eth.G1.zero_spec`);
* `isInfinity` is the identity, `toAffine` its affine point (`Eth.G1.isInfinity_iff`,
  `Eth.G1.affine_spec`, and G2's), and `neg` the group's negation.

Their tests by vectors are kept; these theorems make EthLib's own formulas proved, which the
equalities of `hash_to_G2` and FastAggregateVerify with EthLib's use.
-/

namespace LeanLight.Lc.Bls

open WeierstrassCurve WeierstrassCurve.Jacobian
open LeanLight.Lc.Bls.Provenance (ofEth)

namespace Eth

open EthLib.Cryptography.Bls (Fp)

local notation "aff1" => Point.toAffine E1
local notation "aff2" => Point.toAffine E2

/-! ## G1 -/

/-- The triple of `𝔽_p` an EthLib `G1` point stands for. -/
def g1J (p : EthLib.Cryptography.Bls.G1) : Fin 3 → GFp := ![(p.x.val : GFp), p.y.val, p.z.val]

@[simp] theorem g1J_0 (p : EthLib.Cryptography.Bls.G1) : g1J p 0 = p.x.val := rfl
@[simp] theorem g1J_1 (p : EthLib.Cryptography.Bls.G1) : g1J p 1 = p.y.val := rfl
@[simp] theorem g1J_2 (p : EthLib.Cryptography.Bls.G1) : g1J p 2 = p.z.val := rfl

/-- EthLib's Fermat exponent, `modulus − 2`, inverts. -/
theorem pow_modulus_sub_two (x : GFp) : x ^ (EthLib.Cryptography.Bls.Fp.modulus - 2) = x⁻¹ :=
  pow_sub_two_eq_inv x

/-- EthLib's `Fp.isZero` is the field's zero test. -/
theorem fp_isZero_iff (a : Fp) : a.isZero = true ↔ (a.val : GFp) = 0 := by
  rw [Fp.isZero, beq_iff_eq, cast_eq_zero (val_lt a)]

/-- EthLib's `Fp.beq` is the field's equality. -/
theorem fp_beq_iff (a b : Fp) : a.beq b = true ↔ (a.val : GFp) = b.val := by
  rw [Fp.beq, beq_iff_eq, cast_inj (val_lt a) (val_lt b)]

namespace G1

open EthLib.Cryptography.Bls.G1 (zero double mulNat neg)

theorem zero_eq : g1J zero = Jac.inf := by
  funext i; fin_cases i <;> simp [g1J, zero, Jac.inf, Fp.one, Fp.zero]

theorem zero_spec : E1.Nonsingular (g1J zero) ∧ aff1 (g1J zero) = 0 := by
  rw [zero_eq]; exact Jac.inf_spec 4

theorem double_eq (p : EthLib.Cryptography.Bls.G1) : g1J (double p) = Jac.dbl (g1J p) := by
  unfold double Jac.dbl
  by_cases h : p.z.isZero = true
  · rw [ite_eq_left h, ite_eq_left (show g1J p 2 = 0 from (fp_isZero_iff _).mp h)]
  rw [ite_eq_right h, ite_eq_right (show ¬g1J p 2 = 0 from fun e => h ((fp_isZero_iff _).mpr e))]
  funext i
  fin_cases i <;> simp [g1J, Jac.dblF] <;> ring

theorem add_eq (p q : EthLib.Cryptography.Bls.G1) : g1J (EthLib.Cryptography.Bls.G1.add p q) = Jac.add (g1J p) (g1J q) := by
  unfold EthLib.Cryptography.Bls.G1.add Jac.add
  by_cases h1 : p.z.isZero = true
  · rw [ite_eq_left h1, ite_eq_left (show g1J p 2 = 0 from (fp_isZero_iff _).mp h1)]
  rw [ite_eq_right h1, ite_eq_right (show ¬g1J p 2 = 0 from fun e => h1 ((fp_isZero_iff _).mpr e))]
  by_cases h2 : q.z.isZero = true
  · rw [ite_eq_left h2, ite_eq_left (show g1J q 2 = 0 from (fp_isZero_iff _).mp h2)]
  rw [ite_eq_right h2, ite_eq_right (show ¬g1J q 2 = 0 from fun e => h2 ((fp_isZero_iff _).mpr e))]
  dsimp only
  have hu : (p.x * (q.z * q.z)).beq (q.x * (p.z * p.z)) = true ↔
      g1J p 0 * (g1J q 2 * g1J q 2) = g1J q 0 * (g1J p 2 * g1J p 2) := by
    rw [fp_beq_iff]; simp
  have hs : (p.y * q.z * (q.z * q.z)).beq (q.y * p.z * (p.z * p.z)) = true ↔
      g1J p 1 * g1J q 2 * (g1J q 2 * g1J q 2) = g1J q 1 * g1J p 2 * (g1J p 2 * g1J p 2) := by
    rw [fp_beq_iff]; simp
  by_cases h3 : (p.x * (q.z * q.z)).beq (q.x * (p.z * p.z)) = true
  · rw [ite_eq_left h3, ite_eq_left (hu.mp h3)]
    by_cases h4 : (p.y * q.z * (q.z * q.z)).beq (q.y * p.z * (p.z * p.z)) = true
    · rw [ite_eq_left h4, ite_eq_left (hs.mp h4), double_eq]
    · rw [ite_eq_right h4, ite_eq_right (fun e => h4 (hs.mpr e)), zero_eq]
  · rw [ite_eq_right h3, ite_eq_right (fun e => h3 (hu.mpr e))]
    funext i
    fin_cases i <;> simp [g1J, Jac.addF] <;> ring

theorem double_spec {p : EthLib.Cryptography.Bls.G1} (hp : E1.Nonsingular (g1J p)) :
    E1.Nonsingular (g1J (double p)) ∧ aff1 (g1J (double p)) = 2 • aff1 (g1J p) := by
  rw [double_eq]; exact Jac.dbl_spec 4 hp

theorem add_spec {p q : EthLib.Cryptography.Bls.G1} (hp : E1.Nonsingular (g1J p))
    (hq : E1.Nonsingular (g1J q)) :
    E1.Nonsingular (g1J (EthLib.Cryptography.Bls.G1.add p q)) ∧ aff1 (g1J (EthLib.Cryptography.Bls.G1.add p q)) = aff1 (g1J p) + aff1 (g1J q) := by
  rw [add_eq]; exact Jac.add_spec 4 two_ne_zero_GFp hp hq

/-- EthLib's bottom-up double-and-add multiplies. -/
theorem mulNat_spec (k : ℕ) : ∀ {p : EthLib.Cryptography.Bls.G1}, E1.Nonsingular (g1J p) →
    E1.Nonsingular (g1J (mulNat p k)) ∧ aff1 (g1J (mulNat p k)) = k • aff1 (g1J p) := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro p hp
    rw [mulNat]
    by_cases hk : k = 0
    · rw [ite_eq_left hk, hk, zero_smul]; exact zero_spec
    rw [ite_eq_right hk]
    obtain ⟨hd, hd'⟩ := double_spec hp
    obtain ⟨hh, hh'⟩ := ih (k / 2) (by omega) hd
    have hk2 : k = 2 * (k / 2) + k % 2 := (Nat.div_add_mod k 2).symm
    by_cases ho : k % 2 = 1
    · rw [ite_eq_left ho]
      obtain ⟨ha, ha'⟩ := add_spec hp hh
      refine ⟨ha, ?_⟩
      rw [ha', hh', hd', smul_smul]
      conv_rhs => rw [hk2, ho]
      rw [add_smul, one_smul, mul_comm, add_comm]
    · rw [ite_eq_right ho]
      refine ⟨hh, ?_⟩
      rw [hh', hd', smul_smul]
      conv_rhs => rw [hk2, show k % 2 = 0 by omega]
      rw [add_zero, mul_comm]

theorem isInfinity_iff (p : EthLib.Cryptography.Bls.G1) : p.isInfinity = true ↔ g1J p 2 = 0 :=
  fp_isZero_iff _

/-- On a nonsingular point, `isInfinity` is the identity. -/
theorem isInfinity_iff_zero {p : EthLib.Cryptography.Bls.G1} (hn : E1.Nonsingular (g1J p)) :
    p.isInfinity = true ↔ aff1 (g1J p) = 0 := by
  rw [isInfinity_iff]
  constructor
  · intro h; exact Point.toAffine_of_Z_eq_zero h
  · intro h
    by_contra hz
    rw [Point.toAffine_of_Z_ne_zero hn hz] at h
    exact Affine.Point.some_ne_zero _ h

/-- The affine point of a nonsingular point other than the identity, by EthLib's `toAffine`:
nonsingular, and the same point. -/
theorem affine_spec {p : EthLib.Cryptography.Bls.G1} (hn : E1.Nonsingular (g1J p))
    (hz : p.isInfinity = false) :
    E1.Nonsingular ![((p.toAffine).1.val : GFp), (p.toAffine).2.val, 1] ∧
      aff1 ![((p.toAffine).1.val : GFp), (p.toAffine).2.val, 1] = aff1 (g1J p) := by
  have hz' : g1J p 2 ≠ 0 := fun e => by rw [(isInfinity_iff p).mpr e] at hz; cases hz
  have hz0 : p.z.isZero = false := hz
  have hx : (((p.toAffine).1.val : ℕ) : GFp) = g1J p 0 / g1J p 2 ^ 2 := by
    simp only [EthLib.Cryptography.Bls.G1.toAffine, hz0, Bool.false_eq_true, ↓reduceIte, cast_val_mul,
      EthLib.Cryptography.Bls.Fp.inverse]
    rw [cast_val_powNat, pow_modulus_sub_two]; simp [div_eq_mul_inv, sq]
  have hy : (((p.toAffine).2.val : ℕ) : GFp) = g1J p 1 / g1J p 2 ^ 3 := by
    simp only [EthLib.Cryptography.Bls.G1.toAffine, hz0, Bool.false_eq_true, ↓reduceIte, cast_val_mul,
      EthLib.Cryptography.Bls.Fp.inverse]
    rw [cast_val_powNat, pow_modulus_sub_two]; simp only [g1J_1, g1J_2, div_eq_mul_inv]; ring
  rw [hx, hy]
  have hna : E1.Nonsingular ![g1J p 0 / g1J p 2 ^ 2, g1J p 1 / g1J p 2 ^ 3, 1] := by
    rw [nonsingular_some]; exact (nonsingular_of_Z_ne_zero hz').mp hn
  exact ⟨hna, by rw [Point.toAffine_some hna, Point.toAffine_of_Z_ne_zero hn hz']⟩

theorem neg_spec {p : EthLib.Cryptography.Bls.G1} (hn : E1.Nonsingular (g1J p)) :
    E1.Nonsingular (g1J (EthLib.Cryptography.Bls.G1.neg p)) ∧ aff1 (g1J (EthLib.Cryptography.Bls.G1.neg p)) = -aff1 (g1J p) := by
  have e : g1J (EthLib.Cryptography.Bls.G1.neg p) = E1.neg (g1J p) := by
    funext i; fin_cases i <;> simp [g1J, EthLib.Cryptography.Bls.G1.neg, neg_X, neg_Y, neg_Z, negY]
  rw [e]
  exact ⟨nonsingular_neg hn, Point.toAffine_neg hn⟩

end G1

/-! ## G2 -/

/-- The triple of `𝔽_{p²}` an EthLib `G2` point stands for. -/
noncomputable def g2J (p : EthLib.Cryptography.Bls.G2) : Fin 3 → GFp2 :=
  ![(ofEth p.x).toGF, (ofEth p.y).toGF, (ofEth p.z).toGF]

@[simp] theorem g2J_0 (p : EthLib.Cryptography.Bls.G2) : g2J p 0 = (ofEth p.x).toGF := rfl
@[simp] theorem g2J_1 (p : EthLib.Cryptography.Bls.G2) : g2J p 1 = (ofEth p.y).toGF := rfl
@[simp] theorem g2J_2 (p : EthLib.Cryptography.Bls.G2) : g2J p 2 = (ofEth p.z).toGF := rfl

/-- EthLib's `Fp2.isZero` is the field's zero test. -/
theorem fp2_isZero_iff (a : EthLib.Cryptography.Bls.Fp2) :
    a.isZero = true ↔ (ofEth a).toGF = 0 := by
  rw [← Fp2.isZero_iff (Fp2.reduced_ofEth a)]
  simp [EthLib.Cryptography.Bls.Fp2.isZero, Fp.isZero, Fp2.isZero, ofEth]

/-- EthLib's `Fp2.beq` is the field's equality. -/
theorem fp2_beq_iff (a b : EthLib.Cryptography.Bls.Fp2) :
    a.beq b = true ↔ (ofEth a).toGF = (ofEth b).toGF := by
  rw [EthLib.Cryptography.Bls.Fp2.beq, Bool.and_eq_true, fp_beq_iff, fp_beq_iff,
    QuadraticAlgebra.ext_iff]
  rfl

/-- EthLib's small constants `n` lifted into `Fp2`. -/
@[simp] theorem toGF_ofEth_ofFp_ofNat (n : ℕ) :
    (ofEth (EthLib.Cryptography.Bls.Fp2.ofFp (Fp.ofNat n))).toGF = (n : GFp2) := by
  ext
  · simp [ofEth, Fp2.toGF, EthLib.Cryptography.Bls.Fp2.ofFp]
  · simp [ofEth, Fp2.toGF, EthLib.Cryptography.Bls.Fp2.ofFp, Fp.zero]

@[simp] theorem toGF_ofEth_one : (ofEth EthLib.Cryptography.Bls.Fp2.one).toGF = 1 := by
  ext <;> simp [ofEth, Fp2.toGF, EthLib.Cryptography.Bls.Fp2.one, Fp.one, Fp.zero]

@[simp] theorem toGF_ofEth_zero : (ofEth EthLib.Cryptography.Bls.Fp2.zero).toGF = 0 := by
  ext <;> simp [ofEth, Fp2.toGF, EthLib.Cryptography.Bls.Fp2.zero, Fp.zero]

/-- Pushes `ofEth`'s reading in `𝔽_{p²}` through EthLib's `Fp2` operations. -/
macro "eth2_push" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp only [Fp2.toGF_ofEth_add, Fp2.toGF_ofEth_sub, Fp2.toGF_ofEth_neg, Fp2.toGF_ofEth_mul,
    Fp2.toGF_ofEth_inverse, toGF_ofEth_ofFp_ofNat, toGF_ofEth_one, toGF_ofEth_zero] $(loc)?)

namespace G2

open EthLib.Cryptography.Bls.G2 (zero double mulNat)

theorem zero_eq : g2J zero = Jac.inf := by
  funext i; fin_cases i <;> simp [g2J, zero, Jac.inf]

theorem zero_spec : E2.Nonsingular (g2J zero) ∧ aff2 (g2J zero) = 0 := by
  rw [zero_eq]; exact Jac.inf_spec _

theorem double_eq (p : EthLib.Cryptography.Bls.G2) : g2J (double p) = Jac.dbl (g2J p) := by
  unfold double Jac.dbl
  by_cases h : p.z.isZero = true
  · rw [ite_eq_left h, ite_eq_left (show g2J p 2 = 0 from (fp2_isZero_iff _).mp h)]
  rw [ite_eq_right h, ite_eq_right (show ¬g2J p 2 = 0 from fun e => h ((fp2_isZero_iff _).mpr e))]
  funext i
  fin_cases i <;> simp only [g2J, Jac.dblF] <;> eth2_push <;> simp <;> push_cast <;> ring

theorem add_eq (p q : EthLib.Cryptography.Bls.G2) : g2J (EthLib.Cryptography.Bls.G2.add p q) = Jac.add (g2J p) (g2J q) := by
  unfold EthLib.Cryptography.Bls.G2.add Jac.add
  by_cases h1 : p.z.isZero = true
  · rw [ite_eq_left h1, ite_eq_left (show g2J p 2 = 0 from (fp2_isZero_iff _).mp h1)]
  rw [ite_eq_right h1, ite_eq_right (show ¬g2J p 2 = 0 from fun e => h1 ((fp2_isZero_iff _).mpr e))]
  by_cases h2 : q.z.isZero = true
  · rw [ite_eq_left h2, ite_eq_left (show g2J q 2 = 0 from (fp2_isZero_iff _).mp h2)]
  rw [ite_eq_right h2, ite_eq_right (show ¬g2J q 2 = 0 from fun e => h2 ((fp2_isZero_iff _).mpr e))]
  dsimp only
  have hu : (p.x * (q.z * q.z)).beq (q.x * (p.z * p.z)) = true ↔
      g2J p 0 * (g2J q 2 * g2J q 2) = g2J q 0 * (g2J p 2 * g2J p 2) := by
    rw [fp2_beq_iff]; eth2_push; simp
  have hs : (p.y * q.z * (q.z * q.z)).beq (q.y * p.z * (p.z * p.z)) = true ↔
      g2J p 1 * g2J q 2 * (g2J q 2 * g2J q 2) = g2J q 1 * g2J p 2 * (g2J p 2 * g2J p 2) := by
    rw [fp2_beq_iff]; eth2_push; simp
  by_cases h3 : (p.x * (q.z * q.z)).beq (q.x * (p.z * p.z)) = true
  · rw [ite_eq_left h3, ite_eq_left (hu.mp h3)]
    by_cases h4 : (p.y * q.z * (q.z * q.z)).beq (q.y * p.z * (p.z * p.z)) = true
    · rw [ite_eq_left h4, ite_eq_left (hs.mp h4), double_eq]
    · rw [ite_eq_right h4, ite_eq_right (fun e => h4 (hs.mpr e)), zero_eq]
  · rw [ite_eq_right h3, ite_eq_right (fun e => h3 (hu.mpr e))]
    funext i
    fin_cases i <;> simp only [g2J, Jac.addF] <;> eth2_push <;> simp <;> push_cast <;> ring

theorem double_spec {p : EthLib.Cryptography.Bls.G2} (hp : E2.Nonsingular (g2J p)) :
    E2.Nonsingular (g2J (double p)) ∧ aff2 (g2J (double p)) = 2 • aff2 (g2J p) := by
  rw [double_eq]; exact Jac.dbl_spec _ hp

theorem add_spec {p q : EthLib.Cryptography.Bls.G2} (hp : E2.Nonsingular (g2J p))
    (hq : E2.Nonsingular (g2J q)) :
    E2.Nonsingular (g2J (EthLib.Cryptography.Bls.G2.add p q)) ∧ aff2 (g2J (EthLib.Cryptography.Bls.G2.add p q)) = aff2 (g2J p) + aff2 (g2J q) := by
  rw [add_eq]; exact Jac.add_spec _ two_ne_zero_GFp2 hp hq

/-- EthLib's bottom-up double-and-add multiplies. -/
theorem mulNat_spec (k : ℕ) : ∀ {p : EthLib.Cryptography.Bls.G2}, E2.Nonsingular (g2J p) →
    E2.Nonsingular (g2J (mulNat p k)) ∧ aff2 (g2J (mulNat p k)) = k • aff2 (g2J p) := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro p hp
    rw [mulNat]
    by_cases hk : k = 0
    · rw [ite_eq_left hk, hk, zero_smul]; exact zero_spec
    rw [ite_eq_right hk]
    obtain ⟨hd, hd'⟩ := double_spec hp
    obtain ⟨hh, hh'⟩ := ih (k / 2) (by omega) hd
    have hk2 : k = 2 * (k / 2) + k % 2 := (Nat.div_add_mod k 2).symm
    by_cases ho : k % 2 = 1
    · rw [ite_eq_left ho]
      obtain ⟨ha, ha'⟩ := add_spec hp hh
      refine ⟨ha, ?_⟩
      rw [ha', hh', hd', smul_smul]
      conv_rhs => rw [hk2, ho]
      rw [add_smul, one_smul, mul_comm, add_comm]
    · rw [ite_eq_right ho]
      refine ⟨hh, ?_⟩
      rw [hh', hd', smul_smul]
      conv_rhs => rw [hk2, show k % 2 = 0 by omega]
      rw [add_zero, mul_comm]

theorem isInfinity_iff (p : EthLib.Cryptography.Bls.G2) : p.isInfinity = true ↔ g2J p 2 = 0 :=
  fp2_isZero_iff _

/-- On a nonsingular point, `isInfinity` is the identity. -/
theorem isInfinity_iff_zero {p : EthLib.Cryptography.Bls.G2} (hn : E2.Nonsingular (g2J p)) :
    p.isInfinity = true ↔ aff2 (g2J p) = 0 := by
  rw [isInfinity_iff]
  constructor
  · intro h; exact Point.toAffine_of_Z_eq_zero h
  · intro h
    by_contra hz
    rw [Point.toAffine_of_Z_ne_zero hn hz] at h
    exact Affine.Point.some_ne_zero _ h

/-- The affine point of a nonsingular point other than the identity, by EthLib's `toAffine`:
nonsingular, and the same point. -/
theorem affine_spec {p : EthLib.Cryptography.Bls.G2} (hn : E2.Nonsingular (g2J p))
    (hz : p.isInfinity = false) :
    E2.Nonsingular ![(ofEth (p.toAffine).1).toGF, (ofEth (p.toAffine).2).toGF, 1] ∧
      aff2 ![(ofEth (p.toAffine).1).toGF, (ofEth (p.toAffine).2).toGF, 1] = aff2 (g2J p) := by
  have hz' : g2J p 2 ≠ 0 := fun e => by rw [(isInfinity_iff p).mpr e] at hz; cases hz
  have hz0 : p.z.isZero = false := hz
  have hx : (ofEth (p.toAffine).1).toGF = g2J p 0 / g2J p 2 ^ 2 := by
    simp only [EthLib.Cryptography.Bls.G2.toAffine, hz0, Bool.false_eq_true, ↓reduceIte]
    eth2_push; simp [div_eq_mul_inv, sq]
  have hy : (ofEth (p.toAffine).2).toGF = g2J p 1 / g2J p 2 ^ 3 := by
    simp only [EthLib.Cryptography.Bls.G2.toAffine, hz0, Bool.false_eq_true, ↓reduceIte]
    eth2_push; simp only [g2J_1, g2J_2, div_eq_mul_inv]; ring
  rw [hx, hy]
  have hna : E2.Nonsingular ![g2J p 0 / g2J p 2 ^ 2, g2J p 1 / g2J p 2 ^ 3, 1] := by
    rw [nonsingular_some]; exact (nonsingular_of_Z_ne_zero hz').mp hn
  exact ⟨hna, by rw [Point.toAffine_some hna, Point.toAffine_of_Z_ne_zero hn hz']⟩

end G2

end Eth

end LeanLight.Lc.Bls
