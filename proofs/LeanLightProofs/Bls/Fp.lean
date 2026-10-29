import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import LeanLightProofs.Bls.Primes
import LeanLightProofs.Vendor.EthLib.Bls.Fp

/-!
# BLS12-381: the runtime's `Fp` arithmetic is `ZMod p`'s, and EthLib's (25c)

`LeanLight.Bls` computes in the base field on `Nat`s below `P` (`fadd`, `fsub`, `fneg`, `fmul`,
`fsqr`, `fdbl`, `fpow` by `Nat.powMod`, `finv` by Fermat, `fsqrt?` and `fIsSquare`). Here each is
read in the field `GFp = ZMod P` through the cast `ℕ → ZMod P`:

* **Bounds** (`fadd_lt` and the like): every operation keeps its result below `P` when its
  arguments are, so the runtime's values are exactly the field's elements (`cast_inj`).
* **Arithmetic** (`cast_fadd` and the like): the cast of each result is the field operation on
  the casts of the arguments; `finv` is the field's inverse (`0` to `0`), `fpow` its power.
* **Square roots** (`fsqrt?_some`, `fsqrt?_isSome_iff`, `fIsSquare_iff`): `fsqrt?` returns only
  roots, and returns one exactly when its argument is a square; `fIsSquare` is Euler's criterion,
  true exactly on the squares (zero included). `neg_one_not_square`: `−1` is not a square, as
  `P ≡ 3 (mod 4)`.
* **EthLib's readable layer** (`fadd_val` and the like), whose `Fp` is `Fin p`: on the values of
  its elements, each runtime operation gives the value of EthLib's, including its square
  root (`fsqrt?_val`), whose correctness follows (EthLib's own proof of it is replaced by this).
-/

namespace LeanLight.Lc.Bls

/-- The base field `𝔽_p`, `ZMod P`: what `LeanLight.Bls`'s `Nat` arithmetic below `P` computes in. -/
abbrev GFp := ZMod P

/-- EthLib's modulus is the runtime's. -/
theorem modulus_eq : EthLib.Cryptography.Bls.Fp.modulus = P := rfl

theorem P_mod_four : P % 4 = 3 := by decide

theorem one_lt_P : 1 < P := by decide

/-! ## Bounds -/

section Bounds

variable {a b : ℕ}

theorem fadd_lt (ha : a < P) (hb : b < P) : fadd a b < P := by
  dsimp only [fadd]; split <;> omega

theorem fsub_lt (ha : a < P) : fsub a b < P := by
  dsimp only [fsub]; split <;> omega

theorem fneg_lt (ha : a < P) : fneg a < P := by
  dsimp only [fneg]; split <;> omega

theorem fmul_lt : fmul a b < P := Nat.mod_lt _ (by decide)

theorem fsqr_lt : fsqr a < P := Nat.mod_lt _ (by decide)

theorem fdbl_lt (ha : a < P) : fdbl a < P := fadd_lt ha ha

theorem fpow_lt (e : ℕ) : fpow a e < P := by
  rw [fpow, Nat.powMod_def]; exact Nat.mod_lt _ (by decide)

theorem finv_lt : finv a < P := fpow_lt _

end Bounds

/-! ## Arithmetic -/

section Cast

variable (a b : ℕ)

@[simp] theorem cast_fadd : ((fadd a b : ℕ) : GFp) = a + b := by
  dsimp only [fadd]; split
  · rename_i h; rw [Nat.cast_sub h, ZMod.natCast_self, sub_zero, Nat.cast_add]
  · rw [Nat.cast_add]

theorem cast_fsub {b : ℕ} (hb : b ≤ P) : ((fsub a b : ℕ) : GFp) = a - b := by
  dsimp only [fsub]; split
  · rename_i h; rw [Nat.cast_sub h]
  · rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, add_zero]

theorem cast_fneg {a : ℕ} (ha : a ≤ P) : ((fneg a : ℕ) : GFp) = -a := by
  dsimp only [fneg]; split
  · rename_i h; simp [h]
  · rw [Nat.cast_sub ha, ZMod.natCast_self, zero_sub]

@[simp] theorem cast_fmul : ((fmul a b : ℕ) : GFp) = a * b := by
  rw [fmul, ZMod.natCast_mod, Nat.cast_mul]

@[simp] theorem cast_fsqr : ((fsqr a : ℕ) : GFp) = a * a := by
  rw [fsqr, ZMod.natCast_mod, Nat.cast_mul]

@[simp] theorem cast_fdbl : ((fdbl a : ℕ) : GFp) = a + a := cast_fadd a a

@[simp] theorem cast_fpow (e : ℕ) : ((fpow a e : ℕ) : GFp) = (a : GFp) ^ e := by
  rw [fpow, Nat.powMod_def, ZMod.natCast_mod, Nat.cast_pow]

/-- In `ZMod P`, `x^(P−2)` is the inverse (Fermat), `0` included. -/
theorem pow_sub_two_eq_inv (x : GFp) : x ^ (P - 2) = x⁻¹ := by
  by_cases h : x = 0
  · subst h; rw [zero_pow (by decide), inv_zero]
  · refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, show P - 2 + 1 = P - 1 by decide]
    exact ZMod.pow_card_sub_one_eq_one h

@[simp] theorem cast_finv : ((finv a : ℕ) : GFp) = (a : GFp)⁻¹ := by
  rw [finv, cast_fpow, pow_sub_two_eq_inv]

/-- Two values below `P` are equal exactly when their casts are. -/
theorem cast_inj {a b : ℕ} (ha : a < P) (hb : b < P) : (a : GFp) = b ↔ a = b := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

/-- A value below `P` is zero in the field exactly when it is `0`. -/
theorem cast_eq_zero {a : ℕ} (ha : a < P) : (a : GFp) = 0 ↔ a = 0 := by
  rw [← Nat.cast_zero, cast_inj ha (by decide)]

end Cast

/-! ## Square roots and Euler's criterion -/

/-- `−1` is not a square in `𝔽_p`, since `p ≡ 3 (mod 4)`. -/
theorem neg_one_not_square : ¬IsSquare (-1 : GFp) := by
  rw [ZMod.exists_sq_eq_neg_one_iff]; decide

/-- Euler's criterion in `𝔽_p`: a nonzero `x` is a square exactly when `x^((P−1)/2) = 1`. -/
theorem isSquare_iff_pow {x : GFp} (hx : x ≠ 0) : IsSquare x ↔ x ^ ((P - 1) / 2) = 1 := by
  rw [ZMod.euler_criterion P hx, show P / 2 = (P - 1) / 2 by decide]

/-- `fIsSquare` is Euler's criterion: true exactly when `a` is a square in `𝔽_p`, zero
included. -/
theorem fIsSquare_iff (a : ℕ) : fIsSquare a = true ↔ IsSquare (a : GFp) := by
  rw [fIsSquare, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  by_cases h : (a : GFp) = 0
  · have : a % P = 0 := Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff a P).mp h)
    simp [this, h]
  · have h' : a % P ≠ 0 := fun h0 => h (by rw [← ZMod.natCast_mod, h0, Nat.cast_zero])
    rw [isSquare_iff_pow h, ← cast_inj (fpow_lt _) (by decide), cast_fpow, Nat.cast_one]
    simp [h']

/-- What `fsqrt?` returns is a root of its argument, below `P`. -/
theorem fsqrt?_some {a y : ℕ} (h : fsqrt? a = some y) : y < P ∧ (y : GFp) * y = a := by
  dsimp only [fsqrt?] at h
  split at h
  · rename_i hy; cases h
    refine ⟨fpow_lt _, ?_⟩
    rw [← Nat.cast_mul, ← ZMod.natCast_mod, hy, ZMod.natCast_mod]
  · cases h

/-- `x^((P+1)/4)` squares to `x` whenever `x` is a square. -/
theorem pow_sqrt_exp_sq {x : GFp} (hx : IsSquare x) : x ^ ((P + 1) / 4) * x ^ ((P + 1) / 4) = x := by
  obtain ⟨b, rfl⟩ := hx
  rw [← pow_add, ← sq b, ← pow_mul]
  by_cases hb : b = 0
  · subst hb; rw [zero_pow two_ne_zero, zero_pow (by decide)]
  · rw [show 2 * ((P + 1) / 4 + (P + 1) / 4) = P - 1 + 2 by decide, pow_add,
      ZMod.pow_card_sub_one_eq_one hb, one_mul, pow_two]

/-- `fsqrt?` finds a root exactly when its argument is a square in `𝔽_p`. -/
theorem fsqrt?_isSome_iff (a : ℕ) : (fsqrt? a).isSome ↔ IsSquare (a : GFp) := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp h
    exact ⟨y, (fsqrt?_some hy).2.symm⟩
  · intro hsq
    dsimp only [fsqrt?]
    rw [ite_eq_left]
    · rfl
    · rw [← ZMod.natCast_eq_natCast_iff', Nat.cast_mul, cast_fpow]
      exact pow_sqrt_exp_sq hsq

/-! ## EthLib's `Fp`, by values -/

section EthLib

open EthLib.Cryptography.Bls (Fp)

theorem val_lt (a : Fp) : a.val < P := a.isLt

@[simp] theorem cast_val_add (a b : Fp) : (((a + b : Fp).val : ℕ) : GFp) = a.val + b.val := by
  show (((a.val + b.val) % P : ℕ) : GFp) = _
  rw [ZMod.natCast_mod, Nat.cast_add]

@[simp] theorem cast_val_mul (a b : Fp) : (((a * b : Fp).val : ℕ) : GFp) = a.val * b.val := by
  show (((a.val * b.val) % P : ℕ) : GFp) = _
  rw [ZMod.natCast_mod, Nat.cast_mul]

@[simp] theorem cast_val_sub (a b : Fp) : (((a - b : Fp).val : ℕ) : GFp) = a.val - b.val := by
  show ((((P - b.val) + a.val) % P : ℕ) : GFp) = _
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub (le_of_lt (val_lt b)), ZMod.natCast_self]
  ring

@[simp] theorem cast_val_neg (a : Fp) : (((-a : Fp).val : ℕ) : GFp) = -(a.val : GFp) := by
  rw [Fin.val_neg]
  split
  · rename_i h; simp [h]
  · show ((P - a.val : ℕ) : GFp) = _
    rw [Nat.cast_sub (le_of_lt (val_lt a)), ZMod.natCast_self, zero_sub]

@[simp] theorem cast_val_ofNat (n : ℕ) : ((Fp.ofNat n).val : GFp) = n := by
  show ((n % P : ℕ) : GFp) = _
  rw [ZMod.natCast_mod]

/-- An element of EthLib's `Fp` is determined by the cast of its value. -/
theorem fp_ext_iff {a b : Fp} : a = b ↔ (a.val : GFp) = b.val := by
  rw [cast_inj (val_lt a) (val_lt b), Fin.val_inj]

/-- EthLib's square and multiply is the power. -/
theorem cast_val_powNat (a : Fp) (n : ℕ) : ((a.powNat n).val : GFp) = (a.val : GFp) ^ n := by
  induction n using Nat.strongRecOn generalizing a with
  | _ n ih =>
    rw [Fp.powNat]
    split
    · rename_i h; subst h; simp [Fp.one, Nat.cast_one]
    · rename_i h
      have hh := ih (n / 2) (by omega) (a * a)
      split
      · rename_i h2
        rw [cast_val_mul, hh, cast_val_mul, ← pow_two, ← pow_mul, ← pow_succ']
        congr 1; omega
      · rename_i h2
        rw [hh, cast_val_mul, ← pow_two, ← pow_mul]
        congr 1; omega

theorem fadd_val (a b : Fp) : fadd a.val b.val = (a + b).val := by
  rw [← cast_inj (fadd_lt (val_lt a) (val_lt b)) (val_lt _), cast_fadd, cast_val_add]

theorem fsub_val (a b : Fp) : fsub a.val b.val = (a - b).val := by
  rw [← cast_inj (fsub_lt (val_lt a)) (val_lt _), cast_fsub _ (val_lt b).le, cast_val_sub]

theorem fneg_val (a : Fp) : fneg a.val = (-a).val := by
  rw [← cast_inj (fneg_lt (val_lt a)) (val_lt _), cast_fneg (val_lt a).le, cast_val_neg]

theorem fmul_val (a b : Fp) : fmul a.val b.val = (a * b).val := by
  rw [← cast_inj fmul_lt (val_lt _), cast_fmul, cast_val_mul]

/-- The runtime's Fermat inverse is EthLib's (`Fp.inverse`, its own square and multiply). -/
theorem finv_val (a : Fp) : finv a.val = a.inverse.val := by
  rw [← cast_inj finv_lt (val_lt _), cast_finv, Fp.inverse, cast_val_powNat]
  exact (pow_sub_two_eq_inv _).symm

/-- The runtime's `fsqrt?` returns, on the value of `a`, the value of EthLib's `Fp.sqrt a` when
that succeeds, and nothing when it fails. -/
theorem fsqrt?_val (a : Fp) : fsqrt? a.val = (Fp.sqrt a).toOption.map Fin.val := by
  unfold fsqrt? Fp.sqrt
  have hc : ((Fp.powNat a ((Fp.modulus + 1) / 4)).val) = fpow a.val ((P + 1) / 4) := by
    rw [← cast_inj (val_lt _) (fpow_lt _), cast_val_powNat, cast_fpow]; rfl
  have hiff : (fpow a.val ((P + 1) / 4) * fpow a.val ((P + 1) / 4) % P = a.val % P) ↔
      (Fp.powNat a ((Fp.modulus + 1) / 4) * Fp.powNat a ((Fp.modulus + 1) / 4)).beq a = true := by
    rw [Fp.beq, beq_iff_eq, Fin.val_mul, hc, Nat.mod_eq_of_lt (val_lt a)]; rfl
  by_cases h : fpow a.val ((P + 1) / 4) * fpow a.val ((P + 1) / 4) % P = a.val % P
  · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]; simp [Except.toOption, hc]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.mpr h'))]; rfl

end EthLib

end LeanLight.Lc.Bls
