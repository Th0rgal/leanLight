import LeanLightProofs.Bls.Scott

/-!
# BLS12-381: `ψ`'s subgroup test is sound

CoreVerify's signature subgroup check runs as `G2A.inSubgroupFast` (`LeanLight.Bls.G2`): the test
`ψ(Q) = [x]Q` (`x` negative, so `ψ(Q) = −[X]Q`; `G2A.inSubgroupPsi`) by the untwisted Frobenius
endomorphism `ψ = twist⁻¹ ∘ Frobenius ∘ twist` for a point with `x ≠ 0`, and `[r]Q = O` for any
point that test does not accept. This file proves the test sound, so that `inSubgroupFast` is
`inSubgroup` on the curve (`G2A.inSubgroupFast_eq`):

* `psiX` and `psiY` (`LeanLight.Bls.psiX`, `psiY`) satisfy `psiX³ = u` (`psiX_cube`) and
  `psiY² = u` (`psiY_sq`), with `conj(psiX)·psiX = β²` (`psiX_norm`) and `conj(psiY)·psiY = −1`
  (`psiY_norm`), checked by the kernel on the coordinates.
* `ψ(x, y) = (conj(x)·psiX, conj(y)·psiY)` maps `E': y² = x³ + 4(1 + u)` to itself
  (`nonsingular_psi`, since `4(1 − u)·u = 4(1 + u)`) and is a group endomorphism of `E'(𝔽_{p²})`
  (`psi_add`; `psiHom`): `conj` is the field automorphism `star` of `𝔽_{p²}`, and `psiY² = psiX³`
  makes `ψ` scale every chord or tangent slope by `psiY · psiX⁻¹` after `star`, so it commutes with
  the group law.
* Applying `ψ` twice cancels `star` (`star (star z) = z`) and leaves the pure scaling
  `ψ²(x, y) = (ω·x, −y)` (`ω = β²`, `ω² + ω + 1 = 0`), so `ψ⁴(x, y) = (ω²·x, y)`. For `x ≠ 0`, the
  three points `(ω²·x, y)`, `(ω·x, y)` and `(x, y)` have distinct `x`-coordinates and lie on the
  horizontal line `Y = y`, so `ψ⁴(Q) − ψ²(Q) + Q = O` (`psi_cycle`).
* Hence (`psi_sound`) `ψ(Q) = −[X]Q` gives `ψ²(Q) = [X²]Q` and `ψ⁴(Q) = [X⁴]Q`, so
  `[X⁴ − X² + 1]Q = O`, and `X⁴ − X² + 1 = r` (`Scott.R_eq`): `[r]Q = O`.

Only soundness is needed. A point of G2 the test refuses is still accepted, by `[r]Q = O`; that
every point of G2 passes the test (`ψ` acts on G2 as `[−X]`, as `psi_acts` checks on the generator)
is why the slow path never runs on an honest signature, and is not used here.
-/

namespace LeanLight.Lc.Bls

open WeierstrassCurve WeierstrassCurve.Jacobian

namespace Psi

/-- `psiX` is reduced. -/
theorem reduced_psiX : psiX.Reduced := ⟨by decide, by decide⟩

/-- `psiY` is reduced. -/
theorem reduced_psiY : psiY.Reduced := ⟨by decide, by decide⟩

/-- `psiX` in `𝔽_{p²}`. -/
noncomputable abbrev px : GFp2 := psiX.toGF

/-- `psiY` in `𝔽_{p²}`. -/
noncomputable abbrev py : GFp2 := psiY.toGF

/-- `psiX³ = u` in `𝔽_{p²}`. -/
theorem psiX_cube : px ^ 3 = ⟨0, 1⟩ := by
  have h : (psiX.sqr.mul psiX).eq ⟨0, 1⟩ = true := by decide +kernel
  rw [Fp2.eq_iff Fp2.reduced_mul ⟨by decide, by decide⟩,
    Fp2.toGF_mul Fp2.reduced_sqr reduced_psiX, Fp2.toGF_sqr reduced_psiX] at h
  have h0 : (Fp2.mk 0 1).toGF = (⟨0, 1⟩ : GFp2) := by ext <;> simp [Fp2.toGF]
  rw [h0] at h
  linear_combination h

/-- `psiY² = u` in `𝔽_{p²}`. -/
theorem psiY_sq : py ^ 2 = ⟨0, 1⟩ := by
  have h : psiY.sqr.eq ⟨0, 1⟩ = true := by decide +kernel
  rw [Fp2.eq_iff Fp2.reduced_sqr ⟨by decide, by decide⟩, Fp2.toGF_sqr reduced_psiY] at h
  have h0 : (Fp2.mk 0 1).toGF = (⟨0, 1⟩ : GFp2) := by ext <;> simp [Fp2.toGF]
  rw [h0] at h
  linear_combination h

/-- `psiY² = psiX³`. -/
theorem py_sq_eq_px_cube : py ^ 2 = px ^ 3 := psiY_sq.trans psiX_cube.symm

/-- `psiX ≠ 0`. -/
theorem px_ne_zero : px ≠ 0 := by
  intro h
  have hc := psiX_cube
  rw [h, zero_pow (by decide)] at hc
  have := congrArg QuadraticAlgebra.im hc
  exact zero_ne_one this

/-- `psiY ≠ 0`. -/
theorem py_ne_zero : py ≠ 0 := by
  intro h
  have hs := psiY_sq
  rw [h, zero_pow (by decide)] at hs
  have := congrArg QuadraticAlgebra.im hs
  exact zero_ne_one this

/-- `ω = β²` embedded in `𝔽_{p²}`, the primitive cube root of unity `ψ²` scales `x` by. -/
noncomputable abbrev w : GFp2 := ⟨Scott.b ^ 2, 0⟩

/-- `conj(psiX) · psiX = ω` in `𝔽_{p²}`. -/
theorem psiX_norm : star px * px = w := by
  have h : (psiX.conj.mul psiX).eq ⟨fmul beta beta, 0⟩ = true := by decide +kernel
  rw [Fp2.eq_iff Fp2.reduced_mul ⟨fmul_lt, by decide⟩,
    Fp2.toGF_mul (Fp2.reduced_conj reduced_psiX) reduced_psiX,
    Fp2.toGF_conj reduced_psiX] at h
  ext
  · have hr := congrArg QuadraticAlgebra.re h
    simpa [Fp2.toGF, w, cast_fmul, sq] using hr
  · have hi := congrArg QuadraticAlgebra.im h
    simpa [Fp2.toGF, w] using hi

/-- `conj(psiY) · psiY = −1` in `𝔽_{p²}`. -/
theorem psiY_norm : star py * py = -1 := by
  have h : ((psiY.conj.mul psiY).add Fp2.one).isZero = true := by decide +kernel
  rw [Fp2.isZero_iff (Fp2.reduced_add Fp2.reduced_mul Fp2.reduced_one), Fp2.toGF_add,
    Fp2.toGF_one, Fp2.toGF_mul (Fp2.reduced_conj reduced_psiY) reduced_psiY,
    Fp2.toGF_conj reduced_psiY] at h
  linear_combination h

/-- `ω² + ω + 1 = 0` in `𝔽_{p²}`. -/
theorem w_sq_add : w ^ 2 + w + 1 = 0 := by
  ext
  · simp only [w, sq, QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_one,
      QuadraticAlgebra.re_zero, mul_zero]
    linear_combination (Scott.b ^ 2 - Scott.b + 1) * Scott.b_sq_add
  · simp [w, sq, QuadraticAlgebra.im_one]

/-- `ω³ = 1`. -/
theorem w_cube : w ^ 3 = 1 := by linear_combination (w - 1) * w_sq_add

theorem w_ne_zero : w ≠ 0 := by
  intro h
  have := w_cube
  rw [h] at this
  simp at this

theorem w_ne_one : w ≠ 1 := by
  intro h
  have := w_sq_add
  rw [h, one_pow] at this
  have hr := congrArg QuadraticAlgebra.re this
  simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_one, QuadraticAlgebra.re_zero] at hr
  have h3 : ((3 : ℕ) : GFp) = 0 := by push_cast; linear_combination hr
  rw [cast_eq_zero (by decide)] at h3
  exact absurd h3 (by decide)

/-- `star` is a ring endomorphism of `𝔽_{p²}`: `star (a * b) = star a * star b` (`𝔽_{p²}` is
commutative). -/
theorem star_mul' (a b : GFp2) : star (a * b) = star a * star b := by
  rw [star_mul, mul_comm]

theorem star_pow' (a : GFp2) (n : ℕ) : star (a ^ n) = (star a) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, star_mul', ih, pow_succ]

theorem star_div' (a b : GFp2) : star (a / b) = star a / star b := by
  ext <;> simp [div_eq_mul_inv, QuadraticAlgebra.inv_def]
  ring

/-- `star (4(1 + u)) · u = 4(1 + u)`. -/
theorem star_bTwist_mul_u : star (⟨4, 4⟩ : GFp2) * ⟨0, 1⟩ = ⟨4, 4⟩ := by
  ext <;> simp

/-- `E'` as an affine curve, whose points form the group. -/
abbrev A : WeierstrassCurve.Affine GFp2 := E2.toAffine

theorem negY_eq (x y : GFp2) : A.negY x y = -y := by simp [Affine.negY]

/-- On `E'`, a point is nonsingular exactly when it is on the curve. -/
theorem nonsingular_iff {x y : GFp2} : A.Nonsingular x y ↔ y ^ 2 = x ^ 3 + ⟨4, 4⟩ :=
  (nonsingular_some (W' := E2) x y).symm.trans E2_nonsingular_iff

theorem nonsingular_psi {x y : GFp2} (h : A.Nonsingular x y) :
    A.Nonsingular (star x * px) (star y * py) := by
  rw [nonsingular_iff] at *
  have hs : (star y) ^ 2 = (star x) ^ 3 + star (⟨4, 4⟩ : GFp2) := by
    have := congrArg star h
    rwa [star_pow', star_add, star_pow'] at this
  calc (star y * py) ^ 2 = (star y) ^ 2 * py ^ 2 := by ring
    _ = ((star x) ^ 3 + star (⟨4, 4⟩ : GFp2)) * ⟨0, 1⟩ := by rw [hs, psiY_sq]
    _ = (star x) ^ 3 * px ^ 3 + star (⟨4, 4⟩ : GFp2) * ⟨0, 1⟩ := by rw [add_mul, psiX_cube]
    _ = (star x * px) ^ 3 + ⟨4, 4⟩ := by rw [star_bTwist_mul_u]; ring

theorem nonsingular_scale {x y : GFp2} (h : A.Nonsingular x y) : A.Nonsingular (w * x) y := by
  rw [nonsingular_iff] at *
  linear_combination h - x ^ 3 * w_cube

theorem nonsingular_scale_neg {x y : GFp2} (h : A.Nonsingular x y) :
    A.Nonsingular (w * x) (-y) := by
  rw [nonsingular_iff] at *
  linear_combination h - x ^ 3 * w_cube

/-- `ψ(x, y) = (conj(x)·psiX, conj(y)·psiY)` on `E'(𝔽_{p²})`, the identity fixed. -/
noncomputable def psi : A.Point → A.Point
  | 0 => 0
  | .some x y h => .some (star x * px) (star y * py) (nonsingular_psi h)

/-- `ψ` maps every slope `m` to `star m · py · px⁻¹`. -/
theorem slope_psi (x₁ x₂ y₁ y₂ : GFp2) :
    A.slope (star x₁ * px) (star x₂ * px) (star y₁ * py) (star y₂ * py) =
      star (A.slope x₁ x₂ y₁ y₂) * py * px⁻¹ := by
  have hpx := px_ne_zero
  have hpy := py_ne_zero
  by_cases hx : x₁ = x₂
  · subst hx
    by_cases hy : y₁ = A.negY x₁ y₂
    · have hy' : star y₁ * py = A.negY (star x₁ * px) (star y₂ * py) := by
        rw [negY_eq] at hy ⊢; rw [hy, star_neg, neg_mul]
      rw [Affine.slope_of_Y_eq rfl hy', Affine.slope_of_Y_eq rfl hy, star_zero, zero_mul, zero_mul]
    · have hy' : star y₁ * py ≠ A.negY (star x₁ * px) (star y₂ * py) := by
        rw [negY_eq] at hy ⊢
        intro e
        apply hy
        have e' : star y₁ = -(star y₂) := mul_right_cancel₀ hpy (by linear_combination e)
        simpa using congrArg star e'
      rw [Affine.slope_of_Y_ne rfl hy', Affine.slope_of_Y_ne rfl hy]
      simp only [negY_eq, mul_zero, zero_mul, add_zero, sub_zero, sub_neg_eq_add]
      rw [star_div', star_mul', star_ofNat, star_pow', star_add]
      by_cases hy0 : star y₁ + star y₁ = 0
      · have hy0' : star y₁ * py + star y₁ * py = 0 := by rw [← add_mul, hy0, zero_mul]
        rw [hy0, hy0', div_zero, div_zero, zero_mul, zero_mul]
      · have hpxi : px * px⁻¹ = 1 := mul_inv_cancel₀ hpx
        have hpyi : py * py⁻¹ = 1 := mul_inv_cancel₀ hpy
        calc 3 * (star x₁ * px) ^ 2 / (star y₁ * py + star y₁ * py)
            = 3 * (star x₁ * px) ^ 2 * ((star y₁ + star y₁) * py)⁻¹ := by
                rw [div_eq_mul_inv, add_mul]
          _ = 3 * star x₁ ^ 2 * (star y₁ + star y₁)⁻¹ * px ^ 2 * py⁻¹ := by
                rw [mul_inv]; ring
          _ = 3 * star x₁ ^ 2 * (star y₁ + star y₁)⁻¹ * (px ^ 2 * (px * px⁻¹)) * py⁻¹ := by
                rw [hpxi, mul_one]
          _ = 3 * star x₁ ^ 2 * (star y₁ + star y₁)⁻¹ * (py ^ 2 * px⁻¹) * py⁻¹ := by
                have h3 : px ^ 2 * (px * px⁻¹) = py ^ 2 * px⁻¹ := by
                  linear_combination -px⁻¹ * py_sq_eq_px_cube
                rw [h3]
          _ = 3 * star x₁ ^ 2 * (star y₁ + star y₁)⁻¹ * py * (py * py⁻¹) * px⁻¹ := by ring
          _ = 3 * star x₁ ^ 2 / (star y₁ + star y₁) * py * px⁻¹ := by
                rw [hpyi, mul_one, div_eq_mul_inv]
  · have hx' : star x₁ * px ≠ star x₂ * px := by
      intro e
      apply hx
      have e' : star x₁ = star x₂ := mul_right_cancel₀ hpx e
      simpa using congrArg star e'
    rw [Affine.slope_of_X_ne hx', Affine.slope_of_X_ne hx, star_div', star_sub, star_sub]
    have h1 : star x₁ - star x₂ ≠ 0 := sub_ne_zero.mpr fun e => hx (by simpa using congrArg star e)
    have h2 : star x₁ * px - star x₂ * px ≠ 0 := sub_ne_zero.mpr hx'
    field_simp

/-- `ψ` commutes with the chord-and-tangent law. -/
theorem psi_add (P Q : A.Point) : psi (P + Q) = psi P + psi Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · exact (zero_add (psi (.some x₂ y₂ h₂))).symm ▸ (congrArg psi (zero_add _)).trans rfl
  · exact (add_zero (psi (.some x₁ y₁ h₁))).symm ▸ (congrArg psi (add_zero _)).trans rfl
  have hpx := px_ne_zero
  have hpy := py_ne_zero
  by_cases hxy : x₁ = x₂ ∧ y₁ = A.negY x₂ y₂
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
    show (0 : A.Point) =
      Affine.Point.some (star x₁ * px) (star y₁ * py) _ +
        Affine.Point.some (star x₂ * px) (star y₂ * py) _
    rw [Affine.Point.add_of_Y_eq (by rw [hxy.1])
      (by rw [negY_eq]; rw [negY_eq] at hxy; rw [hxy.2, star_neg, neg_mul])]
  · have hxy' : ¬(star x₁ * px = star x₂ * px ∧
        star y₁ * py = A.negY (star x₂ * px) (star y₂ * py)) := by
      rintro ⟨h1, h2⟩
      apply hxy
      rw [negY_eq] at h2 ⊢
      have hx' : star x₁ = star x₂ := mul_right_cancel₀ hpx h1
      have hy' : star y₁ = -(star y₂) := mul_right_cancel₀ hpy (by linear_combination h2)
      exact ⟨by simpa using congrArg star hx', by simpa using congrArg star hy'⟩
    rw [Affine.Point.add_some hxy]
    show Affine.Point.some _ _ _ =
      Affine.Point.some (star x₁ * px) (star y₁ * py) _ +
        Affine.Point.some (star x₂ * px) (star y₂ * py) _
    rw [Affine.Point.add_some hxy', Affine.Point.some.injEq]
    simp only [Affine.addX, Affine.addY, Affine.negAddY, negY_eq, slope_psi, zero_mul, add_zero,
      sub_zero]
    have hpxi : px * px⁻¹ = 1 := mul_inv_cancel₀ hpx
    have hm2 : (py * px⁻¹) ^ 2 = px := by
      calc (py * px⁻¹) ^ 2 = py ^ 2 * (px⁻¹) ^ 2 := by ring
        _ = px ^ 3 * (px⁻¹) ^ 2 := by rw [py_sq_eq_px_cube]
        _ = px * (px * px⁻¹) ^ 2 := by ring
        _ = px := by rw [hpxi]; ring
    have hm3 : (py * px⁻¹) ^ 3 = py := by
      calc (py * px⁻¹) ^ 3 = (py * px⁻¹) ^ 2 * (py * px⁻¹) := by ring
        _ = py * (px * px⁻¹) := by rw [hm2]; ring
        _ = py := by rw [hpxi, mul_one]
    simp only [star_sub, star_add, star_neg, star_mul', star_pow']
    set s := star (A.slope x₁ x₂ y₁ y₂)
    constructor
    · linear_combination -s ^ 2 * hm2
    · linear_combination s ^ 3 * hm3 - s * (2 * star x₁ + star x₂) * py * hpxi

/-- `ψ` as a homomorphism of `E'(𝔽_{p²})`. -/
noncomputable def psiHom : A.Point →+ A.Point where
  toFun := psi
  map_zero' := rfl
  map_add' := psi_add

/-- `ψ²(x, y) = (ω·x, −y)`: applying `ψ` twice cancels `star` and scales `x` by `ω` and `y` by
`−1`. -/
theorem psi_two {x y : GFp2} (h : A.Nonsingular x y) :
    psi (psi (.some x y h)) = .some (w * x) (-y) (nonsingular_scale_neg h) := by
  show Affine.Point.some (star (star x * px) * px) (star (star y * py) * py) _ = _
  rw [Affine.Point.some.injEq]
  rw [star_mul', star_star, star_mul', star_star]
  exact ⟨by linear_combination x * psiX_norm, by linear_combination y * psiY_norm⟩

/-- `ψ⁴(x, y) = (ω²·x, y)`. -/
theorem psi_four {x y : GFp2} (h : A.Nonsingular x y) :
    psi (psi (psi (psi (.some x y h)))) =
      .some (w * (w * x)) y (nonsingular_scale (nonsingular_scale h)) := by
  rw [psi_two h, psi_two (nonsingular_scale_neg h), Affine.Point.some.injEq]
  exact ⟨rfl, neg_neg y⟩

/-- For `Q = (x, y)` with `x ≠ 0`, `ψ⁴(Q) − ψ²(Q) + Q = O`: `(ω²x, y)`, `(ωx, y)` and `(x, y)` are
the three points of `E'` on the line `Y = y` (`−ψ²(Q) = (ωx, y)`). -/
theorem psi_cycle {x y : GFp2} (h : A.Nonsingular x y) (hx : x ≠ 0) :
    psi (psi (psi (psi (.some x y h)))) - psi (psi (.some x y h)) + .some x y h = 0 := by
  rw [psi_four h, psi_two h, sub_eq_add_neg]
  have hneg : -(.some (w * x) (-y) (nonsingular_scale_neg h) : A.Point) =
      .some (w * x) y (nonsingular_scale h) := by
    rw [Affine.Point.neg_some, Affine.Point.some.injEq]
    exact ⟨rfl, by rw [negY_eq, neg_neg]⟩
  rw [hneg]
  have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr w_ne_one
  have hne : w * x ≠ x := by
    intro e
    apply hw1
    have : (w - 1) * x = 0 := by linear_combination e
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · exact absurd h' hx
  show Affine.Point.some (w * (w * x)) y _ + Affine.Point.some (w * x) y _ +
    Affine.Point.some x y h = 0
  rw [Affine.Point.add_of_X_ne (by
      intro e; apply hne
      exact mul_left_cancel₀ w_ne_zero e)]
  rw [Affine.Point.add_of_Y_eq]
  · simp only [Affine.addX, Affine.slope_of_X_ne (show w * (w * x) ≠ w * x from fun e =>
      hne (mul_left_cancel₀ w_ne_zero e)), sub_self, zero_div]
    linear_combination -x * w_sq_add
  · simp only [Affine.addY, Affine.negAddY, negY_eq, Affine.slope_of_X_ne (show w * (w * x) ≠ w * x
      from fun e => hne (mul_left_cancel₀ w_ne_zero e)), sub_self, zero_div, zero_mul, zero_add]

/-- **`ψ`'s test is sound**: a point `Q = (x, y)` of `E'` with `x ≠ 0` and `ψ(Q) = −[X]Q` has
`[r]Q = O`. -/
theorem psi_sound {x y : GFp2} (h : A.Nonsingular x y) (hx : x ≠ 0)
    (hs : psi (.some x y h) = -(X • (.some x y h : A.Point))) :
    R • (.some x y h : A.Point) = 0 := by
  set Q : A.Point := .some x y h
  have h1 : psiHom Q = -(X • Q) := hs
  have h2 : psi (psi Q) = (X * X) • Q := by
    change psiHom (psiHom Q) = _
    rw [h1, map_neg, map_nsmul, h1]
    simp only [← neg_nsmul, neg_neg, smul_smul]
  have h4 : psi (psi (psi (psi Q))) = (X * X * (X * X)) • Q := by
    have h2' : psiHom (psiHom Q) = (X * X) • Q := h2
    change psiHom (psiHom (psiHom (psiHom Q))) = _
    rw [h2', map_nsmul, map_nsmul, h2', smul_smul]
  have hc := psi_cycle h hx
  rw [h4, h2] at hc
  have key : (R + X * X) • Q = (X * X) • Q := by
    rw [Scott.R_eq, add_smul, one_smul]
    rw [← sub_eq_zero, ← hc]
    abel
  rw [add_smul] at key
  exact add_eq_right.mp key

end Psi

/-! ## The runtime's test -/

namespace G2J

/-- The runtime's negation is the group's. -/
theorem neg_spec {p : G2J} (hp : p.Reduced) (hn : E2.Nonsingular p.toJ) :
    p.neg.Reduced ∧ E2.Nonsingular p.neg.toJ ∧
      Point.toAffine E2 p.neg.toJ = -Point.toAffine E2 p.toJ := by
  have he : p.neg.toJ = E2.neg p.toJ := by
    funext i
    fin_cases i <;> simp [toJ, neg, Jacobian.neg, Jacobian.negY, Fp2.toGF_neg hp.2.1]
  refine ⟨⟨hp.1, Fp2.reduced_neg hp.2.1, hp.2.2⟩, by rw [he]; exact nonsingular_neg hn, ?_⟩
  rw [he, Point.toAffine_neg hn]

/-- The runtime's equality test is sound: two reduced nonsingular triples it calls equal stand
for one point. -/
theorem eq_sound {p q : G2J} (hp : p.Reduced) (hq : q.Reduced) (hnp : E2.Nonsingular p.toJ)
    (hnq : E2.Nonsingular q.toJ) (h : p.eq q = true) :
    Point.toAffine E2 p.toJ = Point.toAffine E2 q.toJ := by
  unfold eq at h
  by_cases hpz : p.z.isZero = true
  · rw [ite_eq_left hpz] at h
    rw [Point.toAffine_of_Z_eq_zero ((Fp2.isZero_iff hp.2.2).mp hpz),
      Point.toAffine_of_Z_eq_zero ((Fp2.isZero_iff hq.2.2).mp h)]
  rw [ite_eq_right hpz] at h
  by_cases hqz : q.z.isZero = true
  · rw [ite_eq_left hqz] at h; cases h
  rw [ite_eq_right hqz, Bool.and_eq_true,
    Fp2.eq_iff Fp2.reduced_mul Fp2.reduced_mul,
    Fp2.eq_iff Fp2.reduced_mul Fp2.reduced_mul] at h
  obtain ⟨hx1, hy1, hz1⟩ := hp
  obtain ⟨hx2, hy2, hz2⟩ := hq
  fp2_push at h
  obtain ⟨h1, h2⟩ := h
  have hpz' : p.toJ 2 ≠ 0 := fun e => hpz ((Fp2.isZero_iff hz1).mpr e)
  have hqz' : q.toJ 2 ≠ 0 := fun e => hqz ((Fp2.isZero_iff hz2).mpr e)
  rw [Point.toAffine_of_Z_ne_zero hnp hpz', Point.toAffine_of_Z_ne_zero hnq hqz',
    Affine.Point.some.injEq]
  simp only [toJ_0, toJ_1, toJ_2] at hpz' hqz' ⊢
  constructor
  · field_simp
    linear_combination h1
  · field_simp
    linear_combination h2

end G2J

namespace G2A

/-- **`ψ`'s test, as it runs, is sound**: a reduced point of `E'` with `x ≠ 0` that
`inSubgroupPsi` accepts has `[r]Q = O`. -/
theorem inSubgroupPsi_sound {p : G2A} (hp : p.Reduced) (hn : E2.Nonsingular p.toJ)
    (hx : p.x.isZero = false) (h : p.inSubgroupPsi = true) : p.inSubgroup = true := by
  rw [inSubgroup_iff hp hn]
  have hna : Psi.A.Nonsingular p.x.toGF p.y.toGF := (nonsingular_some (W' := E2) _ _).mp hn
  have hP : Point.toAffine E2 p.toJ = .some p.x.toGF p.y.toGF hna := Point.toAffine_some hn
  -- ψ(p), as the runtime computes it
  let ps := (G2J.ofAffine p).psi
  have hsr : ps.Reduced :=
    ⟨Fp2.reduced_mul, Fp2.reduced_mul, Fp2.reduced_conj Fp2.reduced_one⟩
  have hsj : ps.toJ = ![star p.x.toGF * Psi.px, star p.y.toGF * Psi.py, 1] := by
    funext i
    fin_cases i
    · simp [ps, G2J.psi, G2J.ofAffine, G2J.toJ,
        Fp2.toGF_mul (Fp2.reduced_conj hp.1) Psi.reduced_psiX, Fp2.toGF_conj hp.1]
    · simp [ps, G2J.psi, G2J.ofAffine, G2J.toJ,
        Fp2.toGF_mul (Fp2.reduced_conj hp.2) Psi.reduced_psiY, Fp2.toGF_conj hp.2]
    · simp [ps, G2J.psi, G2J.ofAffine, G2J.toJ, Fp2.toGF_conj Fp2.reduced_one]
  have hsn : E2.Nonsingular ps.toJ := by
    rw [hsj, nonsingular_some]; exact Psi.nonsingular_psi hna
  have hs : Point.toAffine E2 ps.toJ = Psi.psi (Point.toAffine E2 p.toJ) := by
    rw [hP]
    show _ = Affine.Point.some _ _ _
    rw [show ps.toJ = ![star p.x.toGF * Psi.px, star p.y.toGF * Psi.py, 1] from hsj]
    exact Point.toAffine_some (hsj ▸ hsn)
  -- [X]p, then its negation
  obtain ⟨hmr, hmj⟩ := G2J.toJ_mulA hp X
  obtain ⟨hmn, hma⟩ := Jac.mulA_spec (⟨4, 4⟩ : GFp2) two_ne_zero_GFp2 hn X
  rw [← hmj] at hmn hma
  obtain ⟨hnr, hnn, hna'⟩ := G2J.neg_spec hmr hmn
  have he := G2J.eq_sound hsr hnr hsn hnn h
  rw [hs, hna', hma] at he
  change _ = -(X • Point.toAffine E2 p.toJ) at he
  rw [hP] at he
  have hx' : p.x.toGF ≠ 0 := fun h0 => by
    rw [(Fp2.isZero_iff hp.1).mpr h0] at hx; cases hx
  rw [hP]
  exact Psi.psi_sound hna hx' he

/-- **What runs is CoreVerify's subgroup check**: on a reduced point of `E'`, `inSubgroupFast`
(`ψ`'s test for `x ≠ 0`, else `[r]Q = O`) is `inSubgroup` (`[r]Q = O`). -/
theorem inSubgroupFast_eq {p : G2A} (hp : p.Reduced) (hn : E2.Nonsingular p.toJ) :
    p.inSubgroupFast = p.inSubgroup := by
  unfold inSubgroupFast
  by_cases hs : (!p.x.isZero && p.inSubgroupPsi) = true
  · rw [hs, Bool.true_or]
    rw [Bool.and_eq_true, Bool.not_eq_true'] at hs
    exact (inSubgroupPsi_sound hp hn hs.1 hs.2).symm
  · rw [Bool.not_eq_true] at hs
    rw [hs, Bool.false_or]

end G2A

end LeanLight.Lc.Bls
