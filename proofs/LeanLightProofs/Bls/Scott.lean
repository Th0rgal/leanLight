import LeanLightProofs.Bls.Curves

/-!
# BLS12-381: Scott's subgroup test is sound

KeyValidate's subgroup check runs as `G1A.inSubgroupFast` (`LeanLight.Bls.G1`): Scott's test
`σ(P) = [−x²]P` (eprint 2021/1130 §6) for a point with `x ≠ 0`, and `[r]P = O` for any point that
test does not accept. This file proves the test sound, so that `inSubgroupFast` is `inSubgroup`
on the curve (`G1A.inSubgroupFast_eq`):

* `β` (`LeanLight.Bls.beta`) is a primitive cube root of unity of `𝔽_p`: `β² + β + 1 = 0`
  (`b_sq_add`), checked by the kernel on the number.
* `σ(x, y) = (β·x, y)` maps `E: y² = x³ + 4` to itself (`β³ = 1`) and is a group endomorphism of
  `E(𝔽_p)` (`sigma_add`; `sigmaHom`): it multiplies every slope by `β²`, so it commutes with the
  chord-and-tangent law.
* For a point `P = (x, y)` with `x ≠ 0`, `σ²(P) + σ(P) + P = O` (`sigma_cycle`): the three points
  `(x, y)`, `(βx, y)`, `(β²x, y)` lie on the horizontal line through `P`.
* Hence (`scott_sound`) `σ(P) = −[x²]P` gives `σ²(P) = [x⁴]P`, so `[x⁴ − x² + 1]P = O`, and
  `x⁴ − x² + 1 = r` (`R_eq`): `[r]P = O`.

Only soundness is needed. A point of G1 the test refuses is still accepted, by `[r]P = O`; that
every point of G1 passes the test (`σ` acts on G1 as `[−x²]`, as `beta_acts` checks on the
generator) is why the slow path never runs on an honest key, and is not used here.
-/

namespace LeanLight.Lc.Bls

open WeierstrassCurve WeierstrassCurve.Jacobian

namespace Scott

/-- `β` in `𝔽_p`. -/
noncomputable abbrev b : GFp := (beta : GFp)

/-- `β² + β + 1 = 0`. -/
theorem b_sq_add : b ^ 2 + b + 1 = 0 := by
  have h : ((beta * beta + beta + 1 : ℕ) : GFp) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    decide +kernel
  push_cast at h
  linear_combination h

/-- `β³ = 1`. -/
theorem b_cube : b ^ 3 = 1 := by linear_combination (b - 1) * b_sq_add

theorem b_ne_zero : b ≠ 0 := by
  intro h
  have := b_cube
  rw [h] at this
  simp at this

theorem b_ne_one : b ≠ 1 := by
  intro h
  have := b_sq_add
  rw [h] at this
  have h3 : ((3 : ℕ) : GFp) = 0 := by push_cast; linear_combination this
  rw [cast_eq_zero (by decide)] at h3
  exact absurd h3 (by decide)

/-- `E` as an affine curve, whose points form the group. -/
abbrev A : WeierstrassCurve.Affine GFp := E1.toAffine

theorem a₁ : A.a₁ = 0 := rfl
theorem a₂ : A.a₂ = 0 := rfl
theorem a₃ : A.a₃ = 0 := rfl
theorem a₄ : A.a₄ = 0 := rfl

theorem negY_eq (x y : GFp) : A.negY x y = -y := by simp [Affine.negY, a₁, a₃]

/-- On `E`, a point is nonsingular exactly when it is on the curve. -/
theorem nonsingular_iff {x y : GFp} : A.Nonsingular x y ↔ y ^ 2 = x ^ 3 + 4 :=
  (nonsingular_some (W' := E1) x y).symm.trans E1_nonsingular_iff

theorem nonsingular_sigma {x y : GFp} (h : A.Nonsingular x y) : A.Nonsingular (b * x) y := by
  rw [nonsingular_iff] at *
  linear_combination h - x ^ 3 * b_cube

/-- `σ(x, y) = (β·x, y)` on `E(𝔽_p)`, the identity fixed. -/
noncomputable def sigma : A.Point → A.Point
  | 0 => 0
  | .some x y h => .some (b * x) y (nonsingular_sigma h)

/-- `σ` multiplies the slope of the chord or tangent by `β²`. -/
theorem slope_sigma (x₁ x₂ y₁ y₂ : GFp) :
    A.slope (b * x₁) (b * x₂) y₁ y₂ = b ^ 2 * A.slope x₁ x₂ y₁ y₂ := by
  have hb := b_ne_zero
  by_cases hx : x₁ = x₂
  · subst hx
    by_cases hy : y₁ = A.negY x₁ y₂
    · rw [Affine.slope_of_Y_eq rfl (by rw [negY_eq]; rw [negY_eq] at hy; exact hy),
        Affine.slope_of_Y_eq rfl hy, mul_zero]
    · have hy' : y₁ ≠ A.negY (b * x₁) y₂ := by rw [negY_eq]; rw [negY_eq] at hy; exact hy
      rw [Affine.slope_of_Y_ne rfl hy', Affine.slope_of_Y_ne rfl hy]
      simp only [negY_eq, a₁, a₂, a₄]
      ring
  · have hx' : b * x₁ ≠ b * x₂ := fun h => hx (mul_left_cancel₀ hb h)
    rw [Affine.slope_of_X_ne hx', Affine.slope_of_X_ne hx]
    have h1 : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    have h2 : b * x₁ - b * x₂ ≠ 0 := sub_ne_zero.mpr hx'
    field_simp
    linear_combination -(y₁ - y₂) * b_cube

/-- `σ` commutes with the chord-and-tangent law. -/
theorem sigma_add (P Q : A.Point) : sigma (P + Q) = sigma P + sigma Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · exact (zero_add (sigma (.some x₂ y₂ h₂))).symm ▸ (congrArg sigma (zero_add _)).trans rfl
  · exact (add_zero (sigma (.some x₁ y₁ h₁))).symm ▸ (congrArg sigma (add_zero _)).trans rfl
  have hb := b_ne_zero
  by_cases hxy : x₁ = x₂ ∧ y₁ = A.negY x₂ y₂
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
    show (0 : A.Point) = Affine.Point.some (b * x₁) y₁ _ + Affine.Point.some (b * x₂) y₂ _
    rw [Affine.Point.add_of_Y_eq (by rw [hxy.1]) (by rw [negY_eq]; rw [negY_eq] at hxy; exact hxy.2)]
  · have hxy' : ¬(b * x₁ = b * x₂ ∧ y₁ = A.negY (b * x₂) y₂) := by
      rintro ⟨h1, h2⟩
      exact hxy ⟨mul_left_cancel₀ hb h1, by rw [negY_eq]; rw [negY_eq] at h2; exact h2⟩
    rw [Affine.Point.add_some hxy]
    show Affine.Point.some _ _ _ = Affine.Point.some (b * x₁) y₁ _ + Affine.Point.some (b * x₂) y₂ _
    rw [Affine.Point.add_some hxy', Affine.Point.some.injEq]
    simp only [Affine.addX, Affine.addY, Affine.negAddY, negY_eq, a₁, a₂, slope_sigma]
    constructor
    · linear_combination -b * (A.slope x₁ x₂ y₁ y₂) ^ 2 * b_cube
    · linear_combination ((A.slope x₁ x₂ y₁ y₂) ^ 3 * (b ^ 3 + 1) -
        (A.slope x₁ x₂ y₁ y₂) * (2 * x₁ + x₂)) * b_cube

/-- `σ` as a homomorphism of `E(𝔽_p)`. -/
noncomputable def sigmaHom : A.Point →+ A.Point where
  toFun := sigma
  map_zero' := rfl
  map_add' := sigma_add

/-- For `P = (x, y)` with `x ≠ 0`, `σ²(P) + σ(P) + P = O`: `(x, y)`, `(βx, y)` and `(β²x, y)` are
the three points of `E` on the line `Y = y`. -/
theorem sigma_cycle {x y : GFp} (h : A.Nonsingular x y) (hx : x ≠ 0) :
    sigma (sigma (.some x y h)) + sigma (.some x y h) + .some x y h = 0 := by
  have hb1 : b - 1 ≠ 0 := sub_ne_zero.mpr b_ne_one
  have hne : b * x ≠ x := by
    intro e
    apply hb1
    have : (b - 1) * x = 0 := by linear_combination e
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · exact absurd h' hx
  show Affine.Point.some (b * (b * x)) y _ + Affine.Point.some (b * x) y _ +
    Affine.Point.some x y h = 0
  rw [Affine.Point.add_of_X_ne (by
      intro e; apply hne
      have hb := b_ne_zero
      exact mul_left_cancel₀ hb e)]
  rw [Affine.Point.add_of_Y_eq]
  · simp only [Affine.addX, Affine.slope_of_X_ne (show b * (b * x) ≠ b * x from fun e =>
      hne (mul_left_cancel₀ b_ne_zero e)), sub_self, zero_div, a₁, a₂]
    linear_combination -x * b_sq_add
  · simp only [Affine.addY, Affine.negAddY, negY_eq, Affine.slope_of_X_ne (show b * (b * x) ≠ b * x
      from fun e => hne (mul_left_cancel₀ b_ne_zero e)), sub_self, zero_div, zero_mul, zero_add,
      neg_neg]

/-- `r = x⁴ − x² + 1`. -/
theorem R_eq : R + X * X = X * X * (X * X) + 1 := by decide

/-- **Scott's test is sound**: a point `P = (x, y)` of `E` with `x ≠ 0` and `σ(P) = −[x²]P` has
`[r]P = O`. -/
theorem scott_sound {x y : GFp} (h : A.Nonsingular x y) (hx : x ≠ 0)
    (hs : sigma (.some x y h) = -((X * X) • (.some x y h : A.Point))) :
    R • (.some x y h : A.Point) = 0 := by
  set P : A.Point := .some x y h
  have h2 : sigma (sigma P) = (X * X * (X * X)) • P := by
    change sigmaHom (sigmaHom P) = _
    change sigma P = _ at hs
    rw [show sigmaHom P = sigma P from rfl, hs, map_neg, map_nsmul, show sigmaHom P = sigma P
      from rfl, hs]
    simp only [← neg_nsmul, neg_neg, smul_smul]
  have hc := sigma_cycle h hx
  rw [h2, hs] at hc
  have key : (R + X * X) • P = (X * X) • P := by
    rw [R_eq, add_smul, one_smul]
    rw [← sub_eq_zero, ← hc]
    abel
  rw [add_smul] at key
  exact add_eq_right.mp key

end Scott

/-! ## The runtime's test -/

namespace G1J

/-- The runtime's negation is the group's. -/
theorem neg_spec {p : G1J} (hp : p.Reduced) (hn : E1.Nonsingular p.toJ) :
    p.neg.Reduced ∧ E1.Nonsingular p.neg.toJ ∧
      Point.toAffine E1 p.neg.toJ = -Point.toAffine E1 p.toJ := by
  have he : p.neg.toJ = E1.neg p.toJ := by
    funext i
    fin_cases i <;> simp [toJ, neg, Jacobian.neg, Jacobian.negY, cast_fneg hp.2.1.le]
  refine ⟨⟨hp.1, fneg_lt hp.2.1, hp.2.2⟩, by rw [he]; exact nonsingular_neg hn, ?_⟩
  rw [he, Point.toAffine_neg hn]

/-- The runtime's equality test is sound: two reduced nonsingular triples it calls equal stand
for one point. -/
theorem eq_sound {p q : G1J} (hp : p.Reduced) (hq : q.Reduced) (hnp : E1.Nonsingular p.toJ)
    (hnq : E1.Nonsingular q.toJ) (h : p.eq q = true) :
    Point.toAffine E1 p.toJ = Point.toAffine E1 q.toJ := by
  unfold eq at h
  by_cases hpz : p.z = 0
  · rw [if_pos hpz, decide_eq_true_iff] at h
    rw [Point.toAffine_of_Z_eq_zero (by simp [hpz]), Point.toAffine_of_Z_eq_zero (by simp [h])]
  rw [if_neg hpz] at h
  by_cases hqz : q.z = 0
  · rw [if_pos hqz] at h; cases h
  rw [if_neg hqz, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff,
    nat_eq_iff_cast fmul_lt fmul_lt, nat_eq_iff_cast fmul_lt fmul_lt] at h
  fp_push at h
  obtain ⟨h1, h2⟩ := h
  have hpz' : p.toJ 2 ≠ 0 := by rw [toJ_2, Ne, cast_eq_zero hp.2.2]; exact hpz
  have hqz' : q.toJ 2 ≠ 0 := by rw [toJ_2, Ne, cast_eq_zero hq.2.2]; exact hqz
  rw [Point.toAffine_of_Z_ne_zero hnp hpz', Point.toAffine_of_Z_ne_zero hnq hqz',
    Affine.Point.some.injEq]
  simp only [toJ_0, toJ_1, toJ_2] at hpz' hqz' ⊢
  constructor
  · field_simp
    linear_combination h1
  · field_simp
    linear_combination h2

end G1J

namespace G1A

/-- **Scott's test, as it runs, is sound**: a reduced point of `E` with `x ≠ 0` that
`inSubgroupScott` accepts has `[r]P = O`. -/
theorem inSubgroupScott_sound {p : G1A} (hp : p.Reduced) (hn : E1.Nonsingular p.toJ)
    (hx : p.x ≠ 0) (h : p.inSubgroupScott = true) : p.inSubgroup = true := by
  rw [inSubgroup_iff hp hn]
  have hna : Scott.A.Nonsingular (p.x : GFp) p.y := (nonsingular_some (W' := E1) _ _).mp hn
  have hP : Point.toAffine E1 p.toJ = .some (p.x : GFp) p.y hna := Point.toAffine_some hn
  -- σ(p), as the runtime computes it
  have hsr : (p.sigma).Reduced := ⟨fmul_lt, hp.2, show (1 : ℕ) < P by decide⟩
  have hsj : (p.sigma).toJ = ![Scott.b * p.x, p.y, 1] := by
    funext i; fin_cases i <;> simp [G1A.sigma, G1J.toJ, cast_fmul]
  have hsn : E1.Nonsingular (p.sigma).toJ := by
    rw [hsj, nonsingular_some]; exact Scott.nonsingular_sigma hna
  have hs : Point.toAffine E1 (p.sigma).toJ = Scott.sigma (Point.toAffine E1 p.toJ) := by
    rw [hP]
    show _ = Affine.Point.some _ _ _
    rw [show (p.sigma).toJ = ![Scott.b * p.x, p.y, 1] from hsj]
    exact Point.toAffine_some (hsj ▸ hsn)
  -- [x²]p, then its negation
  obtain ⟨hmr, hmj⟩ := G1J.toJ_mulA hp (X * X)
  obtain ⟨hmn, hma⟩ := Jac.mulA_spec 4 two_ne_zero_GFp hn (X * X)
  rw [← hmj] at hmn hma
  obtain ⟨_, hnn, hna'⟩ := G1J.neg_spec hmr hmn
  have he := G1J.eq_sound hsr (G1J.neg_spec hmr hmn).1 hsn hnn h
  rw [hs, hna', hma] at he
  change _ = -((X * X) • Point.toAffine E1 p.toJ) at he
  rw [hP] at he
  have hx' : (p.x : GFp) ≠ 0 := fun h0 => hx ((cast_eq_zero hp.1).mp h0)
  rw [hP]
  exact Scott.scott_sound hna hx' he

/-- **What runs is KeyValidate's check**: on a reduced point of `E`, `inSubgroupFast` (Scott's
test for `x ≠ 0`, else `[r]P = O`) is `inSubgroup` (`[r]P = O`). -/
theorem inSubgroupFast_eq {p : G1A} (hp : p.Reduced) (hn : E1.Nonsingular p.toJ) :
    p.inSubgroupFast = p.inSubgroup := by
  unfold inSubgroupFast
  by_cases hs : (p.x != 0 && p.inSubgroupScott) = true
  · rw [hs, Bool.true_or]
    rw [Bool.and_eq_true, bne_iff_ne] at hs
    exact (inSubgroupScott_sound hp hn hs.1 hs.2).symm
  · rw [Bool.not_eq_true] at hs
    rw [hs, Bool.false_or]

end G1A

end LeanLight.Lc.Bls
