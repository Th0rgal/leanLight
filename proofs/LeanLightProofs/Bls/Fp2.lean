import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.FieldTheory.Finite.Basic
import LeanLightProofs.Bls.Fp
import LeanLight.Bls.Fp2
import LeanLightProofs.Bls.Provenance

/-!
# BLS12-381: `Fp2` is `𝔽_{p²}`, Mathlib's `QuadraticAlgebra` (25c)

`𝔽_{p²} = 𝔽_p[u]/(u² + 1)` is `GFp2`, Mathlib's `QuadraticAlgebra GFp (−1) 0`, a field since `−1`
is not a square in `𝔽_p` (`neg_one_not_square`), finite with `p²` elements (`card_GFp2`) and of
characteristic `p`. The runtime's `Fp2` (`LeanLight.Bls.Fp2`, two `Nat`s) stands for
`Fp2.toGF a = c0 + c1·u`; `Fp2.Reduced` says both coordinates are below `P`, which every
operation keeps (`Fp2.reduced_mul` and the like), and on which `toGF` is injective
(`Fp2.toGF_inj`), so that `Fp2.eq` and `Fp2.isZero` are the field's equality and zero test.

* **Arithmetic** (`Fp2.toGF_mul` and the like): Karatsuba's multiplication, the complex squaring,
  the inverse through the norm (`0` to `0`), multiplication by `ξ = 1 + u` and by an element of
  `𝔽_p`, and the conjugate (`star`, the Frobenius), on reduced arguments, are the field's.
* **Square roots** (`Fp2.sqrt?_some`, `Fp2.sqrt?_isSome_iff`, `Fp2.isSquare_iff`; `Fp2.sqrt?_eq`
  restates `sqrt?` with `Option.elim` for the kernel's sake, see there): `sqrt?`
  returns only roots of its argument, and returns one exactly when its argument is a square in
  `𝔽_{p²}`; `isSquare`, Euler's criterion on the norm, is true exactly on the squares (zero
  included). `isSquare_iff_norm`: `z` is a square exactly when its norm is one in `𝔽_p`.
* **`ξ`** (`xi_not_square`, `xi_not_cube`): `ξ = 1 + u` is neither a square nor a cube in
  `𝔽_{p²}`, which makes `Fp6` and `Fp12` fields (`LeanLightProofs.Bls.Tower`).
* **EthLib's readable layer** (`Fp2.mul_ofEth` and the like): on EthLib's `Fp2` read as runtime
  values (`Provenance.ofEth`, injective: `Fp2.ofEth_inj`), each runtime operation gives EthLib's:
  Karatsuba's product its schoolbook one, the complex squaring `a * a`, `mulXi` its
  `mulByOnePlusI`, `conj` its `conjugate`, `inv` its `inverse`.
-/

namespace LeanLight.Lc.Bls

open QuadraticAlgebra

/-- `𝔽_{p²} = 𝔽_p[u]/(u² + 1)`: Mathlib's quadratic algebra over `ZMod P` with `u² = −1`. -/
abbrev GFp2 := QuadraticAlgebra GFp (-1) 0

instance fact_neg_one_not_square : Fact (¬IsSquare (-1 : GFp)) := ⟨neg_one_not_square⟩

example : Field GFp2 := inferInstance

instance : Finite GFp2 := Finite.of_equiv _ (QuadraticAlgebra.equivProd _ _).symm

/-- `𝔽_{p²}` has `p²` elements. (Counted with `Nat.card`: with a `Fintype` instance the kernel
compares instances by evaluating them.) -/
theorem card_GFp2 : Nat.card GFp2 = P ^ 2 := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd _ _), Nat.card_prod, Nat.card_zmod, sq]

instance : CharP GFp2 P := charP_of_injective_algebraMap (algebraMap GFp GFp2).injective P

theorem cast_PP : ((PP : ℕ) : GFp) = 0 := by rw [PP, Nat.cast_mul, ZMod.natCast_self, zero_mul]

namespace Fp2

/-- The element `c0 + c1·u` of `𝔽_{p²}` a runtime `Fp2` stands for. -/
def toGF (a : Fp2) : GFp2 := ⟨a.c0, a.c1⟩

/-- Both coordinates are below `P`: a runtime `Fp2` that is an element of `𝔽_{p²}`. -/
def Reduced (a : Fp2) : Prop := a.c0 < P ∧ a.c1 < P

@[simp] theorem re_toGF (a : Fp2) : a.toGF.re = a.c0 := rfl
@[simp] theorem im_toGF (a : Fp2) : a.toGF.im = a.c1 := rfl

/-- On reduced values, `toGF` is injective. -/
theorem toGF_inj {a b : Fp2} (ha : a.Reduced) (hb : b.Reduced) : a.toGF = b.toGF ↔ a = b := by
  obtain ⟨a0, a1⟩ := a; obtain ⟨b0, b1⟩ := b
  simp only [toGF, QuadraticAlgebra.mk.injEq, mk.injEq]
  rw [cast_inj ha.1 hb.1, cast_inj ha.2 hb.2]

theorem reduced_zero : zero.Reduced := ⟨by decide, by decide⟩
theorem reduced_one : one.Reduced := ⟨by decide, by decide⟩

@[simp] theorem toGF_zero : zero.toGF = 0 := by ext <;> simp [toGF, zero]
@[simp] theorem toGF_one : one.toGF = 1 := by ext <;> simp [toGF, one]

/-! ### Bounds -/

section Bounds

variable {a b : Fp2}

theorem reduced_add (ha : a.Reduced) (hb : b.Reduced) : (a.add b).Reduced :=
  ⟨fadd_lt ha.1 hb.1, fadd_lt ha.2 hb.2⟩

theorem reduced_sub (ha : a.Reduced) : (a.sub b).Reduced := ⟨fsub_lt ha.1, fsub_lt ha.2⟩

theorem reduced_neg (ha : a.Reduced) : a.neg.Reduced := ⟨fneg_lt ha.1, fneg_lt ha.2⟩

theorem reduced_dbl (ha : a.Reduced) : a.dbl.Reduced := ⟨fdbl_lt ha.1, fdbl_lt ha.2⟩

theorem reduced_conj (ha : a.Reduced) : a.conj.Reduced := ⟨ha.1, fneg_lt ha.2⟩

theorem reduced_mul : (a.mul b).Reduced :=
  ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩

theorem reduced_sqr : a.sqr.Reduced := ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩

theorem reduced_mulFp (s : ℕ) : (a.mulFp s).Reduced :=
  ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩

theorem reduced_mulXi (ha : a.Reduced) : a.mulXi.Reduced := ⟨fsub_lt ha.1, fadd_lt ha.1 ha.2⟩

theorem reduced_inv : a.inv.Reduced := ⟨Nat.mod_lt _ (by decide), fneg_lt (Nat.mod_lt _ (by decide))⟩

end Bounds

/-! ### Arithmetic -/

section Arith

variable {a b : Fp2}

@[simp] theorem toGF_add : (a.add b).toGF = a.toGF + b.toGF := by
  ext <;> simp [add, toGF]

theorem toGF_sub (hb : b.Reduced) : (a.sub b).toGF = a.toGF - b.toGF := by
  ext
  · simp [sub, toGF, cast_fsub _ hb.1.le]
  · simp [sub, toGF, cast_fsub _ hb.2.le]

theorem toGF_neg (ha : a.Reduced) : a.neg.toGF = -a.toGF := by
  ext
  · simp [neg, toGF, cast_fneg ha.1.le]
  · simp [neg, toGF, cast_fneg ha.2.le]

@[simp] theorem toGF_dbl : a.dbl.toGF = a.toGF + a.toGF := by
  ext <;> simp [dbl, toGF]

/-- The conjugate is `star`, the Frobenius `z ↦ z^p` of `𝔽_{p²}`. -/
theorem toGF_conj (ha : a.Reduced) : a.conj.toGF = star a.toGF := by
  ext
  · simp [conj, toGF]
  · simp [conj, toGF, cast_fneg ha.2.le]

theorem toGF_mul (ha : a.Reduced) (hb : b.Reduced) : (a.mul b).toGF = a.toGF * b.toGF := by
  obtain ⟨a0, a1⟩ := a; obtain ⟨b0, b1⟩ := b
  obtain ⟨ha0, ha1⟩ : a0 < P ∧ a1 < P := ha
  obtain ⟨hb0, hb1⟩ : b0 < P ∧ b1 < P := hb
  have hle : a1 * b1 ≤ a0 * b0 + PP :=
    (Nat.mul_le_mul ha1.le hb1.le).trans (Nat.le_add_left _ _)
  have hk : (a0 + a1) * (b0 + b1) - a0 * b0 - a1 * b1 = a0 * b1 + a1 * b0 := by
    rw [show (a0 + a1) * (b0 + b1) = a0 * b0 + a1 * b1 + (a0 * b1 + a1 * b0) by ring,
      Nat.sub_sub, Nat.add_sub_cancel_left]
  ext
  · simp only [mul, toGF, re_mul]
    rw [ZMod.natCast_mod, Nat.cast_sub hle, Nat.cast_add, cast_PP]
    push_cast; ring
  · simp only [mul, toGF, im_mul]
    rw [hk, ZMod.natCast_mod]
    push_cast; ring

theorem toGF_sqr (ha : a.Reduced) : a.sqr.toGF = a.toGF * a.toGF := by
  obtain ⟨a0, a1⟩ := a
  obtain ⟨ha0, ha1⟩ : a0 < P ∧ a1 < P := ha
  ext
  · simp only [sqr, toGF, re_mul]
    rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_add,
      ZMod.natCast_self]
    ring
  · simp only [sqr, toGF, im_mul]
    rw [ZMod.natCast_mod]
    push_cast; ring

/-- Multiplication by `s` of `𝔽_p`. -/
@[simp] theorem toGF_mulFp (s : ℕ) : (a.mulFp s).toGF = (s : GFp) • a.toGF := by
  ext <;> simp [mulFp, toGF, ZMod.natCast_mod, mul_comm]

/-- `ξ = 1 + u`. -/
@[simp] theorem toGF_xi : xi.toGF = ⟨1, 1⟩ := by ext <;> simp [xi, toGF]

theorem reduced_xi : xi.Reduced := ⟨by decide, by decide⟩

theorem toGF_mulXi (ha : a.Reduced) : a.mulXi.toGF = ⟨1, 1⟩ * a.toGF := by
  ext
  · simp [mulXi, toGF, cast_fsub _ ha.2.le]; ring
  · simp [mulXi, toGF]; ring

theorem toGF_inv : a.inv.toGF = a.toGF⁻¹ := by
  ext
  · simp only [inv, toGF, QuadraticAlgebra.inv_def, re_smul, re_star, norm_def, smul_eq_mul]
    rw [ZMod.natCast_mod, Nat.cast_mul, cast_finv, ZMod.natCast_mod]
    push_cast; ring
  · simp only [inv, toGF, QuadraticAlgebra.inv_def, im_smul, im_star, norm_def, smul_eq_mul]
    rw [cast_fneg (Nat.mod_lt _ (by decide)).le, ZMod.natCast_mod, Nat.cast_mul, cast_finv,
      ZMod.natCast_mod]
    push_cast; ring

/-- `Fp2.eq` is the field's equality, on reduced values. -/
theorem eq_iff (ha : a.Reduced) (hb : b.Reduced) : a.eq b = true ↔ a.toGF = b.toGF := by
  rw [toGF_inj ha hb]
  obtain ⟨a0, a1⟩ := a; obtain ⟨b0, b1⟩ := b
  simp [eq]

/-- `Fp2.isZero` is the field's test for zero, on reduced values. -/
theorem isZero_iff (ha : a.Reduced) : a.isZero = true ↔ a.toGF = 0 := by
  rw [← toGF_zero, toGF_inj ha reduced_zero]
  obtain ⟨a0, a1⟩ := a
  simp [isZero, zero]

end Arith

end Fp2

/-! ## Squares in `𝔽_p` and `𝔽_{p²}` -/

/-- A nonzero `x` of `𝔽_p` that is not a square has `x^((p−1)/2) = −1`. -/
theorem pow_half_of_not_square {x : GFp} (hx : ¬IsSquare x) : x ^ ((P - 1) / 2) = -1 := by
  have h0 : x ≠ 0 := fun h => hx ⟨0, by rw [h, mul_zero]⟩
  rcases ZMod.pow_div_two_eq_neg_one_or_one P h0 with h | h
  · exact absurd ((isSquare_iff_pow h0).mpr (by rwa [show P / 2 = (P - 1) / 2 by decide] at h)) hx
  · rwa [show P / 2 = (P - 1) / 2 by decide] at h

/-- In `𝔽_p`, the product of two non-squares is a square. -/
theorem isSquare_mul_of_not {x y : GFp} (hx : ¬IsSquare x) (hy : ¬IsSquare y) :
    IsSquare (x * y) := by
  have hx0 : x ≠ 0 := fun h => hx ⟨0, by rw [h, mul_zero]⟩
  have hy0 : y ≠ 0 := fun h => hy ⟨0, by rw [h, mul_zero]⟩
  rw [isSquare_iff_pow (mul_ne_zero hx0 hy0), mul_pow, pow_half_of_not_square hx,
    pow_half_of_not_square hy, neg_one_mul, neg_neg]

/-- `(P + 1)/2` is `1/2` in `𝔽_p`. -/
theorem cast_half : (((P + 1) / 2 : ℕ) : GFp) = 2⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [show (2 : GFp) = ((2 : ℕ) : GFp) by norm_num, ← Nat.cast_mul,
    show (P + 1) / 2 * 2 = P + 1 by decide, Nat.cast_add, ZMod.natCast_self, zero_add,
    Nat.cast_one]

theorem two_ne_zero_GFp : (2 : GFp) ≠ 0 := by
  rw [show (2 : GFp) = ((2 : ℕ) : GFp) by norm_num, Ne, cast_eq_zero (by decide)]; decide

/-- The complex method's root: given `g² = a0² + a1²` with `a1 ≠ 0`, and `2·x0² = a0 ± g`,
`x0 ≠ 0` and `x0 + a1·(2x0)⁻¹·u` squares to `a0 + a1·u`. -/
theorem complex_root {a0 a1 g x0 : GFp} (ha1 : a1 ≠ 0) (hg : g * g = a0 * a0 + a1 * a1)
    (hx : 2 * (x0 * x0) = a0 + g ∨ 2 * (x0 * x0) = a0 - g) :
    x0 ≠ 0 ∧ (⟨x0, a1 * (2 * x0)⁻¹⟩ : GFp2) * ⟨x0, a1 * (2 * x0)⁻¹⟩ = ⟨a0, a1⟩ := by
  have h2 := two_ne_zero_GFp
  have hx0 : x0 ≠ 0 := by
    rintro rfl
    apply ha1
    apply mul_self_eq_zero.mp
    rcases hx with h | h
    · linear_combination (-1 : GFp) * hg + (a0 - g) * h
    · linear_combination (-1 : GFp) * hg + (a0 + g) * h
  refine ⟨hx0, ?_⟩
  have hw : 2 * x0 * (2 * x0)⁻¹ = 1 := mul_inv_cancel₀ (mul_ne_zero h2 hx0)
  generalize (2 * x0)⁻¹ = w at hw ⊢
  ext
  · simp only [re_mul]
    refine mul_left_cancel₀ h2 ?_
    rcases hx with h | h
    · linear_combination (1 + 2 * w * w * (g - a0)) * h - (g - a0) * (2 * x0 * w + 1) * hw +
        2 * w * w * hg
    · linear_combination (1 - 2 * w * w * (g + a0)) * h + (g + a0) * (2 * x0 * w + 1) * hw +
        2 * w * w * hg
  · simp only [im_mul]
    linear_combination a1 * hw

/-- In `𝔽_p`, given `g² = a0² + a1²` with `a1 ≠ 0`, one of `(a0 ± g)/2` is a square: their
product is `−(a1/2)²`, not a square since `−1` is not. -/
theorem half_isSquare {a0 a1 g : GFp} (ha1 : a1 ≠ 0) (hg : g * g = a0 * a0 + a1 * a1) :
    IsSquare ((a0 + g) * 2⁻¹) ∨ IsSquare ((a0 - g) * 2⁻¹) := by
  by_contra hno
  push Not at hno
  have hprod := isSquare_mul_of_not hno.1 hno.2
  apply neg_one_not_square
  have h2 := two_ne_zero_GFp
  have hc : (a0 + g) * 2⁻¹ * ((a0 - g) * 2⁻¹) = -1 * ((a1 * 2⁻¹) * (a1 * 2⁻¹)) := by
    linear_combination (-(2⁻¹ * 2⁻¹) : GFp) * hg
  rw [hc] at hprod
  obtain ⟨r, hr⟩ := hprod
  have ha : a1 * 2⁻¹ ≠ 0 := mul_ne_zero ha1 (inv_ne_zero h2)
  generalize a1 * 2⁻¹ = d at hr ha
  refine ⟨r * d⁻¹, ?_⟩
  rw [show r * d⁻¹ * (r * d⁻¹) = (r * r) * (d⁻¹ * d⁻¹) by ring, ← hr]
  field_simp

namespace Fp2

/-- The norm of a runtime `Fp2`'s element, `c0² + c1²`. -/
theorem norm_toGF (a : Fp2) : QuadraticAlgebra.norm a.toGF = (a.c0 : GFp) * a.c0 + a.c1 * a.c1 := by
  rw [norm_def]; simp

/-- The complex method's last step passes its check: `x0 + a1/(2 x0)·u` squares to `a`, when
`2·x0² = a0 ± g` and `g² = a0² + a1²`, `a1 ≠ 0`. -/
theorem sqrt?_check {a : Fp2} {g x0 : ℕ} (ha : a.Reduced) (ha1 : (a.c1 : GFp) ≠ 0)
    (hgg : (g : GFp) * g = a.c0 * a.c0 + a.c1 * a.c1) (hlt : x0 < P)
    (hsq : 2 * ((x0 : GFp) * x0) = a.c0 + g ∨ 2 * ((x0 : GFp) * x0) = a.c0 - g) :
    (sqr ⟨x0, a.c1 * finv (fdbl x0) % P⟩).eq a = true := by
  have hy : (⟨x0, a.c1 * finv (fdbl x0) % P⟩ : Fp2).Reduced := ⟨hlt, Nat.mod_lt _ (by decide)⟩
  obtain ⟨_, hroot⟩ := complex_root ha1 hgg hsq
  rw [eq_iff reduced_sqr ha, toGF_sqr hy]
  have : (⟨x0, a.c1 * finv (fdbl x0) % P⟩ : Fp2).toGF =
      ⟨(x0 : GFp), (a.c1 : GFp) * (2 * (x0 : GFp))⁻¹⟩ := by
    ext
    · rfl
    · simp only [toGF, ZMod.natCast_mod, Nat.cast_mul, cast_finv, cast_fdbl, two_mul]
  rw [this, hroot]; rfl

/-! `sqrt?`'s matches are rewritten to `Option.elim` (`sqrt?_match_1`, `sqrt?_match_3`) before
any case is taken: reducing them in place, by `dsimp` or `split`, has the kernel compare the
match with its reduct, which evaluates `fsqrt?`'s `Nat.powMod` on a symbolic argument and
exhausts its stack. -/

set_option linter.auxLemma false in
/-- `sqrt?`'s match with the `some` case first, as `Option.elim`. -/
theorem sqrt?_match_1 {β : Type} (x : Option ℕ) (f : ℕ → β) (g : Unit → β) :
    Fp2.sqrt?.match_1 (fun _ => β) x f g = x.elim (g ()) f := by cases x <;> rfl

set_option linter.auxLemma false in
/-- `sqrt?`'s match with the `none` case first, as `Option.elim`. -/
theorem sqrt?_match_3 {β : Type} (x : Option ℕ) (n : Unit → β) (f : ℕ → β) :
    Fp2.sqrt?.match_3 (fun _ => β) x n f = x.elim (n ()) f := by cases x <;> rfl

/-- `sqrt?` with its matches as `Option.elim`. -/
theorem sqrt?_eq (a : Fp2) : a.sqrt? =
    if a.c1 = 0 then
      (fsqrt? a.c0).elim ((fsqrt? (fneg a.c0)).elim none fun y => some ⟨0, y⟩)
        fun y => some ⟨y, 0⟩
    else
      (fsqrt? ((a.c0 * a.c0 + a.c1 * a.c1) % P)).elim none fun g =>
        ((fsqrt? (fadd a.c0 g * ((P + 1) / 2) % P)).elim
            (fsqrt? (fsub a.c0 g * ((P + 1) / 2) % P)) some).elim none fun x0 =>
          if (sqr ⟨x0, a.c1 * finv (fdbl x0) % P⟩).eq a = true then
            some ⟨x0, a.c1 * finv (fdbl x0) % P⟩ else none := by
  unfold sqrt?
  simp (config := { iota := false, zeta := false, beta := false, proj := false, decide := false })
    only [sqrt?_match_1, sqrt?_match_3]
  rfl

/-- What `sqrt?` returns is a reduced root of its argument. -/
theorem sqrt?_some {a y : Fp2} (ha : a.Reduced) (h : a.sqrt? = some y) :
    y.Reduced ∧ y.toGF * y.toGF = a.toGF := by
  rw [sqrt?_eq] at h
  by_cases hc1 : a.c1 = 0
  · rw [ite_eq_left hc1] at h
    cases hy0 : fsqrt? a.c0 with
    | some y0 =>
      rw [hy0, Option.elim_some] at h
      cases h
      obtain ⟨hlt, hsq⟩ := fsqrt?_some hy0
      refine ⟨⟨hlt, show 0 < P by decide⟩, ?_⟩
      ext <;> simp [toGF, hsq, hc1]
    | none =>
      rw [hy0, Option.elim_none] at h
      cases hy1 : fsqrt? (fneg a.c0) with
      | some y0 =>
        rw [hy1, Option.elim_some] at h
        cases h
        obtain ⟨hlt, hsq⟩ := fsqrt?_some hy1
        refine ⟨⟨show 0 < P by decide, hlt⟩, ?_⟩
        rw [cast_fneg ha.1.le] at hsq
        ext <;> simp [toGF, hsq, hc1]
      | none => rw [hy1, Option.elim_none] at h; cases h
  · rw [ite_eq_right hc1] at h
    cases hg : fsqrt? ((a.c0 * a.c0 + a.c1 * a.c1) % P) with
    | none => rw [hg, Option.elim_none] at h; cases h
    | some g =>
      rw [hg, Option.elim_some] at h
      have key : ∀ x0, x0 < P →
          (if (sqr ⟨x0, a.c1 * finv (fdbl x0) % P⟩).eq a = true then
            some (⟨x0, a.c1 * finv (fdbl x0) % P⟩ : Fp2) else none) = some y →
          y.Reduced ∧ y.toGF * y.toGF = a.toGF := by
        intro x0 hlt hh
        have hy : (⟨x0, a.c1 * finv (fdbl x0) % P⟩ : Fp2).Reduced :=
          ⟨hlt, Nat.mod_lt _ (by decide)⟩
        by_cases hchk : (sqr ⟨x0, a.c1 * finv (fdbl x0) % P⟩).eq a = true
        · rw [ite_eq_left hchk] at hh
          cases hh
          refine ⟨hy, ?_⟩
          rw [← toGF_sqr hy]
          exact (eq_iff reduced_sqr ha).mp hchk
        · rw [ite_eq_right hchk] at hh; cases hh
      cases h1 : fsqrt? (fadd a.c0 g * ((P + 1) / 2) % P) with
      | some x0 =>
        rw [h1, Option.elim_some, Option.elim_some] at h
        exact key x0 (fsqrt?_some h1).1 h
      | none =>
        rw [h1, Option.elim_none] at h
        cases h2 : fsqrt? (fsub a.c0 g * ((P + 1) / 2) % P) with
        | none => rw [h2, Option.elim_none] at h; cases h
        | some x0 =>
          rw [h2, Option.elim_some] at h
          exact key x0 (fsqrt?_some h2).1 h

/-- `sqrt?` finds a root of every reduced `a` whose norm is a square in `𝔽_p` (and of every `a`
with `c1 = 0`, a square in `𝔽_{p²}` as every element of `𝔽_p` is). -/
theorem sqrt?_isSome_of_norm {a : Fp2} (ha : a.Reduced)
    (hn : IsSquare (QuadraticAlgebra.norm a.toGF)) : a.sqrt?.isSome := by
  rw [sqrt?_eq]
  by_cases hc1 : a.c1 = 0
  · rw [ite_eq_left hc1]
    cases hy0 : fsqrt? a.c0 with
    | some y0 => rfl
    | none =>
      have h0 : ¬IsSquare (a.c0 : GFp) := by
        rw [← fsqrt?_isSome_iff, hy0]; simp
      have hneg : IsSquare ((fneg a.c0 : ℕ) : GFp) := by
        rw [cast_fneg ha.1.le, ← neg_one_mul]
        exact isSquare_mul_of_not neg_one_not_square h0
      obtain ⟨y0, hy1⟩ := Option.isSome_iff_exists.mp ((fsqrt?_isSome_iff _).mpr hneg)
      rw [Option.elim_none, hy1]; rfl
  · rw [ite_eq_right hc1]
    have hnorm : (((a.c0 * a.c0 + a.c1 * a.c1) % P : ℕ) : GFp) =
        QuadraticAlgebra.norm a.toGF := by
      rw [norm_toGF, ZMod.natCast_mod]; push_cast; ring
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp
      ((fsqrt?_isSome_iff _).mpr (hnorm ▸ hn))
    rw [hg, Option.elim_some]
    have ha1 : (a.c1 : GFp) ≠ 0 := by rwa [Ne, cast_eq_zero ha.2]
    obtain ⟨hglt, hgg⟩ := fsqrt?_some hg
    rw [hnorm, norm_toGF] at hgg
    have ht1 : ((fadd a.c0 g * ((P + 1) / 2) % P : ℕ) : GFp) = (a.c0 + g) * 2⁻¹ := by
      rw [ZMod.natCast_mod, Nat.cast_mul, cast_fadd, cast_half]
    have ht2 : ((fsub a.c0 g * ((P + 1) / 2) % P : ℕ) : GFp) = (a.c0 - g) * 2⁻¹ := by
      rw [ZMod.natCast_mod, Nat.cast_mul, cast_fsub _ hglt.le, cast_half]
    have hhalf : ∀ t : GFp, 2 * (t * 2⁻¹) = t := fun t => by
      rw [mul_comm, mul_assoc, inv_mul_cancel₀ two_ne_zero_GFp, mul_one]
    cases h1 : fsqrt? (fadd a.c0 g * ((P + 1) / 2) % P) with
    | some x0 =>
      obtain ⟨hlt, hsq⟩ := fsqrt?_some h1
      rw [Option.elim_some, Option.elim_some,
        ite_eq_left (sqrt?_check ha ha1 hgg hlt (Or.inl (by rw [hsq, ht1, hhalf])))]
      rfl
    | none =>
      have hn1 : ¬IsSquare ((a.c0 + g) * 2⁻¹ : GFp) := by
        rw [← ht1, ← fsqrt?_isSome_iff, h1]; simp
      have hs2 := (half_isSquare ha1 hgg).resolve_left hn1
      rw [← ht2, ← fsqrt?_isSome_iff] at hs2
      obtain ⟨x0, hx0⟩ := Option.isSome_iff_exists.mp hs2
      obtain ⟨hlt, hsq⟩ := fsqrt?_some hx0
      rw [Option.elim_none, hx0, Option.elim_some,
        ite_eq_left (sqrt?_check ha ha1 hgg hlt (Or.inr (by rw [hsq, ht2, hhalf])))]
      rfl

/-- `sqrt?` finds a root exactly when its (reduced) argument is a square in `𝔽_{p²}`. -/
theorem sqrt?_isSome_iff {a : Fp2} (ha : a.Reduced) : a.sqrt?.isSome ↔ IsSquare a.toGF := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp h
    exact ⟨y.toGF, (sqrt?_some ha hy).2.symm⟩
  · rintro ⟨w, hw⟩
    exact sqrt?_isSome_of_norm ha ⟨QuadraticAlgebra.norm w, by rw [hw, map_mul]⟩

/-- The runtime `Fp2` of a field element: its coordinates' values. -/
def ofGF (z : GFp2) : Fp2 := ⟨z.re.val, z.im.val⟩

theorem reduced_ofGF (z : GFp2) : (ofGF z).Reduced :=
  ⟨show z.re.val < P from ZMod.val_lt _, show z.im.val < P from ZMod.val_lt _⟩

@[simp] theorem toGF_ofGF (z : GFp2) : (ofGF z).toGF = z := by
  ext <;> simp [ofGF, toGF, ZMod.natCast_val]

end Fp2

/-- Euler's criterion in `𝔽_{p²}` through the norm: `z` is a square exactly when its norm
`re² + im²` is a square in `𝔽_p`. -/
theorem isSquare_iff_norm (z : GFp2) : IsSquare z ↔ IsSquare (QuadraticAlgebra.norm z) := by
  constructor
  · rintro ⟨w, hw⟩; exact ⟨QuadraticAlgebra.norm w, by rw [hw, map_mul]⟩
  · intro hn
    rw [← Fp2.toGF_ofGF z] at hn ⊢
    exact (Fp2.sqrt?_isSome_iff (Fp2.reduced_ofGF z)).mp
      (Fp2.sqrt?_isSome_of_norm (Fp2.reduced_ofGF z) hn)

namespace Fp2

/-- `isSquare`, Euler's criterion on the norm, is true exactly on the squares of `𝔽_{p²}`. -/
theorem isSquare_iff {a : Fp2} : a.isSquare = true ↔ IsSquare a.toGF := by
  rw [isSquare, fIsSquare_iff, isSquare_iff_norm, norm_toGF, ZMod.natCast_mod]
  push_cast; rfl

end Fp2

/-! ## `ξ = 1 + u` -/

/-- `2` is not a square in `𝔽_p` (`p ≡ 3 mod 8`), by the kernel. -/
theorem two_not_square : ¬IsSquare (2 : GFp) := by
  rw [show (2 : GFp) = ((2 : ℕ) : GFp) by norm_num, ← fIsSquare_iff]
  decide +kernel

/-- `2` is not a cube in `𝔽_p`: `2^((p−1)/3) ≠ 1`, by the kernel. -/
theorem two_not_cube (c : GFp) : c ^ 3 ≠ 2 := by
  intro h
  have hc : c ≠ 0 := by rintro rfl; exact two_ne_zero_GFp (by rw [← h]; ring)
  have h1 : (2 : GFp) ^ ((P - 1) / 3) = 1 := by
    rw [← h, ← pow_mul, show 3 * ((P - 1) / 3) = P - 1 by decide]
    exact ZMod.pow_card_sub_one_eq_one hc
  have h2 : fpow 2 ((P - 1) / 3) = 1 := by
    rw [← cast_inj (fpow_lt _) one_lt_P, cast_fpow, Nat.cast_one]
    exact_mod_cast h1
  revert h2
  decide +kernel

theorem norm_xi : QuadraticAlgebra.norm (⟨1, 1⟩ : GFp2) = 2 := by
  rw [norm_def]; norm_num

/-- `ξ = 1 + u` is not a square in `𝔽_{p²}`: its norm `2` is not one in `𝔽_p`. -/
theorem xi_not_square : ¬IsSquare (⟨1, 1⟩ : GFp2) := by
  rw [isSquare_iff_norm, norm_xi]; exact two_not_square

/-- `ξ = 1 + u` is not a cube in `𝔽_{p²}`: its norm `2` is not one in `𝔽_p`. -/
theorem xi_not_cube (b : GFp2) : b ^ 3 ≠ ⟨1, 1⟩ := by
  intro h
  apply two_not_cube (QuadraticAlgebra.norm b)
  rw [← map_pow, h, norm_xi]

/-! ## EthLib's `Fp2`, by values -/

namespace Fp2

open EthLib.Cryptography.Bls (Fp)
open LeanLight.Lc.Bls.Provenance (ofEth)

/-- EthLib's `Fp2` read as a runtime one is reduced. -/
theorem reduced_ofEth (a : EthLib.Cryptography.Bls.Fp2) : (ofEth a).Reduced :=
  ⟨val_lt a.c0, val_lt a.c1⟩

/-- `ofEth` is injective: EthLib's `Fp2` is determined by its coordinates' values. -/
theorem ofEth_inj {a b : EthLib.Cryptography.Bls.Fp2} : ofEth a = ofEth b ↔ a = b := by
  obtain ⟨a0, a1⟩ := a; obtain ⟨b0, b1⟩ := b
  simp only [ofEth, mk.injEq, EthLib.Cryptography.Bls.Fp2.mk.injEq, Fin.val_inj]

section

variable (a b : EthLib.Cryptography.Bls.Fp2)

theorem toGF_ofEth_add : (ofEth (a + b)).toGF = (ofEth a).toGF + (ofEth b).toGF := by
  ext
  · show (((a.c0 + b.c0 : Fp).val : ℕ) : GFp) = _
    simp [ofEth, toGF]
  · show (((a.c1 + b.c1 : Fp).val : ℕ) : GFp) = _
    simp [ofEth, toGF]

theorem toGF_ofEth_sub : (ofEth (a - b)).toGF = (ofEth a).toGF - (ofEth b).toGF := by
  ext
  · show (((a.c0 - b.c0 : Fp).val : ℕ) : GFp) = _
    simp [ofEth, toGF]
  · show (((a.c1 - b.c1 : Fp).val : ℕ) : GFp) = _
    simp [ofEth, toGF]

theorem toGF_ofEth_neg : (ofEth (-a)).toGF = -(ofEth a).toGF := by
  ext
  · show (((-a.c0 : Fp).val : ℕ) : GFp) = _
    simp [ofEth, toGF]
  · show (((-a.c1 : Fp).val : ℕ) : GFp) = _
    simp [ofEth, toGF]

theorem toGF_ofEth_mul : (ofEth (a * b)).toGF = (ofEth a).toGF * (ofEth b).toGF := by
  ext
  · show (((a.c0 * b.c0 - a.c1 * b.c1 : Fp).val : ℕ) : GFp) = _
    simp [ofEth, toGF]; ring
  · show (((a.c0 * b.c1 + a.c1 * b.c0 : Fp).val : ℕ) : GFp) = _
    simp [ofEth, toGF]

theorem toGF_ofEth_mulByOnePlusI : (ofEth a.mulByOnePlusI).toGF = ⟨1, 1⟩ * (ofEth a).toGF := by
  ext
  · show (((a.c0 - a.c1 : Fp).val : ℕ) : GFp) = _
    simp [ofEth, toGF]; ring
  · show (((a.c0 + a.c1 : Fp).val : ℕ) : GFp) = _
    simp [ofEth, toGF]; ring

theorem toGF_ofEth_conjugate : (ofEth a.conjugate).toGF = star (ofEth a).toGF := by
  ext
  · simp [ofEth, toGF, EthLib.Cryptography.Bls.Fp2.conjugate]
  · show (((-a.c1 : Fp).val : ℕ) : GFp) = _
    simp [ofEth, toGF]

theorem toGF_ofEth_inverse : (ofEth a.inverse).toGF = (ofEth a).toGF⁻¹ := by
  have hinv : (((a.c0 * a.c0 + a.c1 * a.c1 : Fp).inverse.val : ℕ) : GFp) =
      ((a.c0.val : GFp) * a.c0.val + a.c1.val * a.c1.val)⁻¹ := by
    rw [← finv_val, cast_finv]; simp
  ext
  · show (((a.c0 * (a.c0 * a.c0 + a.c1 * a.c1).inverse : Fp).val : ℕ) : GFp) = _
    rw [cast_val_mul, hinv]
    simp [ofEth, toGF, QuadraticAlgebra.inv_def, norm_def]; ring
  · show (((-(a.c1 * (a.c0 * a.c0 + a.c1 * a.c1).inverse) : Fp).val : ℕ) : GFp) = _
    rw [cast_val_neg, cast_val_mul, hinv]
    simp [ofEth, toGF, QuadraticAlgebra.inv_def, norm_def]; ring

/-! The runtime's operations on EthLib's values give EthLib's. -/

theorem add_ofEth : (ofEth a).add (ofEth b) = ofEth (a + b) := by
  rw [← toGF_inj (reduced_add (reduced_ofEth a) (reduced_ofEth b)) (reduced_ofEth _), toGF_add,
    toGF_ofEth_add]

theorem sub_ofEth : (ofEth a).sub (ofEth b) = ofEth (a - b) := by
  rw [← toGF_inj (reduced_sub (reduced_ofEth a)) (reduced_ofEth _), toGF_sub (reduced_ofEth b),
    toGF_ofEth_sub]

theorem neg_ofEth : (ofEth a).neg = ofEth (-a) := by
  rw [← toGF_inj (reduced_neg (reduced_ofEth a)) (reduced_ofEth _), toGF_neg (reduced_ofEth a),
    toGF_ofEth_neg]

/-- Karatsuba's multiplication is EthLib's schoolbook one. -/
theorem mul_ofEth : (ofEth a).mul (ofEth b) = ofEth (a * b) := by
  rw [← toGF_inj reduced_mul (reduced_ofEth _), toGF_mul (reduced_ofEth a) (reduced_ofEth b),
    toGF_ofEth_mul]

theorem sqr_ofEth : (ofEth a).sqr = ofEth (a * a) := by
  rw [← toGF_inj reduced_sqr (reduced_ofEth _), toGF_sqr (reduced_ofEth a), toGF_ofEth_mul]

theorem mulXi_ofEth : (ofEth a).mulXi = ofEth a.mulByOnePlusI := by
  rw [← toGF_inj (reduced_mulXi (reduced_ofEth a)) (reduced_ofEth _),
    toGF_mulXi (reduced_ofEth a), toGF_ofEth_mulByOnePlusI]

theorem conj_ofEth : (ofEth a).conj = ofEth a.conjugate := by
  rw [← toGF_inj (reduced_conj (reduced_ofEth a)) (reduced_ofEth _),
    toGF_conj (reduced_ofEth a), toGF_ofEth_conjugate]

theorem inv_ofEth : (ofEth a).inv = ofEth a.inverse := by
  rw [← toGF_inj reduced_inv (reduced_ofEth _), toGF_inv, toGF_ofEth_inverse]

end

end Fp2

end LeanLight.Lc.Bls
