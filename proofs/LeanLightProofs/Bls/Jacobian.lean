import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
import Mathlib.Tactic.LinearCombination

/-!
# Short Weierstrass curves with `a = 0` in Jacobian coordinates (25c)

One development, over any field, of the formulas `LeanLight.Bls` computes G1 (over `𝔽_p`) and G2
(over `𝔽_{p²}`) with, and later secp256k1's (reuse rule D5): `(X, Y, Z)` stands for the affine
point `(X/Z², Y/Z³)`, `Z = 0` for the identity, on `y² = x³ + b` (`J b`). Ported from EthLib's
`Proofs/Bls/G1Group.lean` (`57af539e`, CC0-1.0), which proves the same formulas for G1 over
`ZMod p`, and shaped as `Spec.EcdsaJacobian` (for `a = −3`) is:

* `dbl`, the EFD's dbl-2009-l with the runtime's shortcut for the identity, is Mathlib's
  `dblXYZ` on the nose (`dblF_eq_dblXYZ`), so it doubles (`dbl_spec`);
* `add`, add-2007-bl with the runtime's shortcuts (an operand the identity; equal `x`: the
  doubling when the `y` agree too, the identity otherwise), is Mathlib's `addXYZ` scaled by
  `−2·Z1·Z2` away from them (`addF_eq_smul_addXYZ`), so it adds (`add_spec`);
* `addA`, madd-2007-bl for an affine second operand, is `add` with `Z2 = 1` (`addA_eq_add`);
* `mulA`, double-and-add from the top bit with mixed additions, multiplies (`mulA_spec`).

Each `*_spec` says: for nonsingular operands the result is nonsingular and its affine point is
the group law's (`Point.toAffine`, Mathlib's `AddCommGroup` on the affine points).
-/

namespace LeanLight.Lc.Bls.Jac

open WeierstrassCurve WeierstrassCurve.Jacobian

variable {F : Type*} [Field F]

/-- `y² = x³ + b` in Jacobian coordinates. -/
abbrev J (b : F) : WeierstrassCurve.Jacobian F := ⟨0, 0, 0, 0, b⟩

/-- The identity's representative `(1, 1, 0)`. -/
def inf : Fin 3 → F := ![1, 1, 0]

/-- dbl-2009-l: `A = X²`, `B = Y²`, `C = B²`, `D = 2((X + B)² − A − C)`, `E = 3A`, `F = E²`,
`X3 = F − 2D`, `Y3 = E(D − X3) − 8C`, `Z3 = 2YZ`. -/
def dblF (P : Fin 3 → F) : Fin 3 → F :=
  ![3 * (P 0 * P 0) * (3 * (P 0 * P 0)) -
      2 * (2 * ((P 0 + P 1 * P 1) * (P 0 + P 1 * P 1) - P 0 * P 0 - P 1 * P 1 * (P 1 * P 1))),
    3 * (P 0 * P 0) *
        (2 * ((P 0 + P 1 * P 1) * (P 0 + P 1 * P 1) - P 0 * P 0 - P 1 * P 1 * (P 1 * P 1)) -
          (3 * (P 0 * P 0) * (3 * (P 0 * P 0)) -
            2 * (2 * ((P 0 + P 1 * P 1) * (P 0 + P 1 * P 1) - P 0 * P 0 -
              P 1 * P 1 * (P 1 * P 1))))) -
      8 * (P 1 * P 1 * (P 1 * P 1)),
    2 * (P 1 * P 2)]

/-- Doubling, with the identity (`Z = 0`) left as it is. -/
def dbl [DecidableEq F] (P : Fin 3 → F) : Fin 3 → F := if P 2 = 0 then P else dblF P

/-- add-2007-bl without its shortcuts: `U1 = X1·Z2²`, `U2 = X2·Z1²`, `S1 = Y1·Z2³`,
`S2 = Y2·Z1³`, `H = U2 − U1`, `I = (2H)²`, `J = H·I`, `r = 2(S2 − S1)`, `V = U1·I`,
`X3 = r² − J − 2V`, `Y3 = r(V − X3) − 2·S1·J`, `Z3 = ((Z1 + Z2)² − Z1² − Z2²)·H`. -/
def addF (P Q : Fin 3 → F) : Fin 3 → F :=
  let z1z1 := P 2 * P 2
  let z2z2 := Q 2 * Q 2
  let u1 := P 0 * z2z2
  let u2 := Q 0 * z1z1
  let s1 := P 1 * Q 2 * z2z2
  let s2 := Q 1 * P 2 * z1z1
  let h := u2 - u1
  let i := 2 * h * (2 * h)
  let j := h * i
  let r := 2 * (s2 - s1)
  let v := u1 * i
  let x3 := r * r - j - 2 * v
  ![x3, r * (v - x3) - 2 * (s1 * j), ((P 2 + Q 2) * (P 2 + Q 2) - z1z1 - z2z2) * h]

/-- Addition with the runtime's shortcuts: an operand the identity gives the other; equal `x`
(`U1 = U2`) gives the doubling when the `y` agree too (`S1 = S2`), the identity otherwise. -/
def add [DecidableEq F] (P Q : Fin 3 → F) : Fin 3 → F :=
  if P 2 = 0 then Q else if Q 2 = 0 then P else
  if P 0 * (Q 2 * Q 2) = Q 0 * (P 2 * P 2) then
    (if P 1 * Q 2 * (Q 2 * Q 2) = Q 1 * P 2 * (P 2 * P 2) then dbl P else inf)
  else addF P Q

/-- madd-2007-bl, the mixed addition of an affine `(x, y)`, with the runtime's shortcuts. -/
def addA [DecidableEq F] (P : Fin 3 → F) (x y : F) : Fin 3 → F :=
  if P 2 = 0 then ![x, y, 1] else
  let z1z1 := P 2 * P 2
  let u2 := x * z1z1
  let s2 := y * P 2 * z1z1
  if P 0 = u2 then (if P 1 = s2 then dbl P else inf) else
  let h := u2 - P 0
  let hh := h * h
  let i := 2 * (2 * hh)
  let j := h * i
  let r := 2 * (s2 - P 1)
  let v := P 0 * i
  let x3 := r * r - j - 2 * v
  ![x3, r * (v - x3) - 2 * (P 1 * j), (P 2 + h) * (P 2 + h) - z1z1 - hh]

/-- One round of `mulA` for the bit `n − 1 − i` of `k`: double, then add `(x, y)` if it is set. -/
def mulStep [DecidableEq F] (x y : F) (k n : ℕ) (acc : Fin 3 → F) (i : ℕ) : Fin 3 → F :=
  if (k >>> (n - 1 - i)) % 2 = 1 then addA (dbl acc) x y else dbl acc

/-- `[k](x, y)`: double-and-add over the `log₂ k + 1` bits of `k`, from the top, from the
identity. -/
def mulA [DecidableEq F] (x y : F) (k : ℕ) : Fin 3 → F :=
  (List.range (Nat.log2 k + 1)).foldl (mulStep x y k (Nat.log2 k + 1)) inf

section Spec

variable (b : F)

local notation "aff" => Point.toAffine (J b)

theorem inf_spec : (J b).Nonsingular inf ∧ aff inf = 0 :=
  ⟨nonsingular_zero, Point.toAffine_zero⟩

/-- dbl-2009-l is Mathlib's `dblXYZ` on `y² = x³ + b`, as polynomials. -/
theorem dblF_eq_dblXYZ (P : Fin 3 → F) : dblF P = (J b).dblXYZ P := by
  funext i
  fin_cases i <;>
    simp [dblF, dblXYZ, dblX, dblY, dblZ, negDblY, negY, dblU_eq] <;> ring

/-- Doubling a nonsingular triple gives a nonsingular triple whose affine point is twice its,
the identity included. -/
theorem dbl_spec [DecidableEq F] {P : Fin 3 → F} (hP : (J b).Nonsingular P) :
    (J b).Nonsingular (dbl P) ∧ aff (dbl P) = 2 • aff P := by
  unfold dbl
  by_cases hz : P 2 = 0
  · rw [ite_eq_left hz, Point.toAffine_of_Z_eq_zero hz, smul_zero]; exact ⟨hP, rfl⟩
  · rw [ite_eq_right hz, dblF_eq_dblXYZ b, ← add_self]
    exact ⟨nonsingular_add hP hP, by rw [Point.toAffine_add hP hP, two_nsmul]⟩

/-- The curve equation of a triple, `Y² = X³ + b·Z⁶`. -/
theorem equation_iff' {P : Fin 3 → F} : (J b).Equation P ↔ P 1 ^ 2 = P 0 ^ 3 + b * P 2 ^ 6 := by
  rw [equation_iff]
  constructor <;> intro h <;> linear_combination h

/-- add-2007-bl is Mathlib's `addXYZ` scaled by `−2·Z1·Z2`, for two triples on the curve. -/
theorem addF_eq_smul_addXYZ {P Q : Fin 3 → F} (hP : (J b).Equation P) (hQ : (J b).Equation Q) :
    addF P Q = (-(2 * (P 2 * Q 2))) • (J b).addXYZ P Q := by
  rw [equation_iff'] at hP hQ
  funext i
  fin_cases i
  · simp only [addF, smul_fin3, addXYZ_X, addX]
    simp
    linear_combination (4 * Q 2 ^ 6) * hP + (4 * P 2 ^ 6) * hQ
  · simp only [addF, smul_fin3, addXYZ_Y, addY, negAddY, negY, addX]
    simp
    linear_combination (8 * Q 2 ^ 6 * (P 1 * Q 2 ^ 3 - Q 1 * P 2 ^ 3)) * hP +
      (8 * P 2 ^ 6 * (P 1 * Q 2 ^ 3 - Q 1 * P 2 ^ 3)) * hQ
  · simp only [addF, smul_fin3, addXYZ_Z, addZ]
    simp
    ring

/-- With its shortcuts, `add` of two nonsingular triples is nonsingular and its affine point is
the sum of theirs (in characteristic other than 2). -/
theorem add_spec [DecidableEq F] (h2 : (2 : F) ≠ 0) {P Q : Fin 3 → F} (hP : (J b).Nonsingular P)
    (hQ : (J b).Nonsingular Q) :
    (J b).Nonsingular (add P Q) ∧ aff (add P Q) = aff P + aff Q := by
  unfold add
  by_cases hPz : P 2 = 0
  · rw [ite_eq_left hPz, Point.toAffine_of_Z_eq_zero hPz, zero_add]; exact ⟨hQ, rfl⟩
  rw [ite_eq_right hPz]
  by_cases hQz : Q 2 = 0
  · rw [ite_eq_left hQz, Point.toAffine_of_Z_eq_zero hQz, add_zero]; exact ⟨hP, rfl⟩
  rw [ite_eq_right hQz]
  by_cases hh : P 0 * (Q 2 * Q 2) = Q 0 * (P 2 * P 2)
  · have hx : P 0 * Q 2 ^ 2 = Q 0 * P 2 ^ 2 := by linear_combination hh
    rw [ite_eq_left hh]
    by_cases hr : P 1 * Q 2 * (Q 2 * Q 2) = Q 1 * P 2 * (P 2 * P 2)
    · have hy : P 1 * Q 2 ^ 3 = Q 1 * P 2 ^ 3 := by linear_combination hr
      rw [ite_eq_left hr, ← Point.toAffine_add hP hQ,
        add_of_equiv (equiv_of_X_eq_of_Y_eq hPz hQz hx hy)]
      obtain ⟨hd, hd'⟩ := dbl_spec b hP
      refine ⟨hd, ?_⟩
      rw [hd', ← dblF_eq_dblXYZ b, Point.toAffine_of_equiv (Setoid.refl _)]
      have := dbl_spec b hP
      unfold dbl at this
      rw [ite_eq_right hPz] at this
      rw [this.2]
    · have hy : P 1 * Q 2 ^ 3 ≠ Q 1 * P 2 ^ 3 := fun e => hr (by linear_combination e)
      rw [ite_eq_right hr]
      refine ⟨(inf_spec b).1, ?_⟩
      rw [(inf_spec b).2, ← Point.toAffine_add hP hQ, add_of_not_equiv (not_equiv_of_Y_ne hy),
        Point.toAffine_of_Z_eq_zero (by rw [addXYZ_Z]; exact addZ_of_X_eq hx)]
  · have hx : P 0 * Q 2 ^ 2 ≠ Q 0 * P 2 ^ 2 := fun e => hh (by linear_combination e)
    rw [ite_eq_right hh]
    have hu : IsUnit (-(2 * (P 2 * Q 2))) := by
      exact (neg_ne_zero.mpr (mul_ne_zero h2 (mul_ne_zero hPz hQz))).isUnit
    rw [addF_eq_smul_addXYZ b hP.1 hQ.1, ← add_of_not_equiv (not_equiv_of_X_ne hx),
      Point.toAffine_smul _ hu, Point.toAffine_add hP hQ, nonsingular_smul _ hu]
    exact ⟨nonsingular_add hP hQ, rfl⟩

/-- madd-2007-bl is add-2007-bl with `Z2 = 1`, shortcuts included. -/
theorem addA_eq_add [DecidableEq F] (P : Fin 3 → F) (x y : F) :
    addA P x y = add P ![x, y, 1] := by
  unfold addA add
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Matrix.cons_val_zero,
    Matrix.cons_val_one, one_ne_zero, ite_false, mul_one]
  by_cases hz : P 2 = 0
  · rw [ite_eq_left hz, ite_eq_left hz]
  rw [ite_eq_right hz, ite_eq_right hz]
  by_cases hx : P 0 = x * (P 2 * P 2)
  · rw [ite_eq_left hx, ite_eq_left hx]
  rw [ite_eq_right hx, ite_eq_right hx]
  funext i
  fin_cases i <;> simp [addF] <;> ring

/-- The mixed addition of a point on the curve: nonsingular, the sum. -/
theorem addA_spec [DecidableEq F] (h2 : (2 : F) ≠ 0) {P : Fin 3 → F} {x y : F}
    (hP : (J b).Nonsingular P) (hq : (J b).Nonsingular ![x, y, 1]) :
    (J b).Nonsingular (addA P x y) ∧ aff (addA P x y) = aff P + aff ![x, y, 1] := by
  rw [addA_eq_add]; exact add_spec b h2 hP hq

/-- Bit `j` of `k` read the runtime's way. -/
theorem shiftRight_succ_bit (k j : ℕ) : k >>> j = 2 * (k >>> (j + 1)) + (k >>> j) % 2 := by
  rw [Nat.shiftRight_succ, Nat.div_add_mod]

/-- After the rounds `0, …, m − 1` of `mulA` over `n` bits (`m ≤ n`, `k < 2ⁿ`), the
accumulator stands for `(k >>> (n − m))·(x, y)`. -/
theorem foldl_mulStep_spec [DecidableEq F] (h2 : (2 : F) ≠ 0) {x y : F}
    (hq : (J b).Nonsingular ![x, y, 1]) (k n : ℕ) (hk : k >>> n = 0) :
    ∀ m, m ≤ n →
      (J b).Nonsingular ((List.range m).foldl (mulStep x y k n) inf) ∧
        aff ((List.range m).foldl (mulStep x y k n) inf) = (k >>> (n - m)) • aff ![x, y, 1] := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨(inf_spec b).1, ?_⟩
    rw [List.range_zero, List.foldl_nil, (inf_spec b).2, Nat.sub_zero, hk, zero_smul]
  | succ m ih =>
    intro hm
    obtain ⟨hacc, hacc'⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range m).foldl (mulStep x y k n) inf = acc at hacc hacc'
    obtain ⟨hd, hd'⟩ := dbl_spec b hacc
    have hbit := shiftRight_succ_bit k (n - 1 - m)
    rw [show n - 1 - m + 1 = n - m by omega] at hbit
    unfold mulStep
    rw [show n - (m + 1) = n - 1 - m by omega]
    rcases Nat.mod_two_eq_zero_or_one (k >>> (n - 1 - m)) with hb | hb
    · rw [ite_eq_right (by omega)]
      refine ⟨hd, ?_⟩
      rw [hd', hacc', smul_smul, hbit, hb, add_zero, mul_comm]
    · rw [ite_eq_left hb]
      obtain ⟨ha, ha'⟩ := addA_spec b h2 hd hq
      refine ⟨ha, ?_⟩
      rw [ha', hd', hacc', smul_smul, hbit, hb, add_smul, one_smul, mul_comm]

/-- `mulA` computes `[k](x, y)` for a point `(x, y)` on the curve. -/
theorem mulA_spec [DecidableEq F] (h2 : (2 : F) ≠ 0) {x y : F}
    (hq : (J b).Nonsingular ![x, y, 1]) (k : ℕ) :
    (J b).Nonsingular (mulA x y k) ∧ aff (mulA x y k) = k • aff ![x, y, 1] := by
  have hk : k >>> (Nat.log2 k + 1) = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt Nat.lt_log2_self
  obtain ⟨h, h'⟩ := foldl_mulStep_spec b h2 hq k (Nat.log2 k + 1) hk (Nat.log2 k + 1) le_rfl
  refine ⟨h, ?_⟩
  unfold mulA
  rw [h', Nat.sub_self, Nat.shiftRight_zero]

end Spec

end LeanLight.Lc.Bls.Jac
