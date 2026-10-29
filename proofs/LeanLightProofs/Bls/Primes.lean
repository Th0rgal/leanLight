import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.Prime
import LeanLight.Bls.Fp

/-!
# BLS12-381: `p` and `r` are prime (25c)

The base field's modulus `P` and the group order `R` of `LeanLight.Bls` are prime (`P_prime`,
`R_prime`), so that `ZMod P` is a field (the instance `fact_P_prime`), on which every later
proof about BLS12-381 rests, and `R` has no factor 3 (`R_coprime_three`), which the cube lemma
needs.

Each proof is Mathlib's Lucas test (`lucas_primality`, through `prime_of_lucas`): a base `a`
and the factorization of `N − 1` as prime powers, with `a^(N−1) = 1` and `a^((N−1)/q) ≠ 1` in
`ZMod N` for each prime `q` of it, evaluated by the kernel (`decide +kernel`; in Lean 4.35 a power
in `ZMod N` is `Nat.powMod`'s square and multiply), so no `native_decide` and no hand-written
modular power. The large `q` are proved prime in turn by their own certificates, the others by
`norm_num`. The certificate for `p` (the factorizations and bases of its Pratt tree) is EthLib's
(`EthLib/Cryptography/Proofs/Bls/FpZMod.lean` at `57af539e`, CC0-1.0), that for `r` the one
measured for the reuse study (`r` is `Fr.modulus`, its `p − 1` smooth).
-/

namespace LeanLight.Lc.Bls

/-- Lucas's test with the factorization of `n − 1` as a list of prime powers `(q, e)`: if their
product is `n − 1`, `a^(n−1) = 1` in `ZMod n`, `a^((n−1)/q) ≠ 1` for each `q`, and every `q` is
prime, then `n` is prime. Mathlib's `lucas_primality`, with the divisors read off the list. -/
theorem prime_of_lucas (n : ℕ) (a : ZMod n) (fs : List (ℕ × ℕ))
    (hprod : (fs.map fun f => f.1 ^ f.2).prod = n - 1) (hpow : a ^ (n - 1) = 1)
    (hdiv : ∀ f ∈ fs, a ^ ((n - 1) / f.1) ≠ 1) (hp : ∀ f ∈ fs, f.1.Prime) : n.Prime := by
  refine lucas_primality n a hpow fun q hq hdvd => ?_
  rw [← hprod] at hdvd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hdvd
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
  obtain rfl : q = f.1 := (Nat.prime_dvd_prime_iff_eq hq (hp f hf)).mp (hq.dvd_of_dvd_pow hqx)
  exact hdiv f hf

/-! ## `p`'s Pratt tree (EthLib's certificate) -/

private theorem prime_9272813673901 : Nat.Prime 9272813673901 :=
  prime_of_lucas _ 2 [(2, 2), (3, 1), (5, 2), (7, 1), (7577, 1), (582767, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> norm_num)

private theorem prime_1928745244171409 : Nat.Prime 1928745244171409 :=
  prime_of_lucas _ 3 [(2, 4), (13, 1), (9272813673901, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> first | exact prime_9272813673901 | norm_num)

private theorem prime_7259797099061183477 : Nat.Prime 7259797099061183477 :=
  prime_of_lucas _ 2 [(2, 2), (941, 1), (1928745244171409, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> first | exact prime_1928745244171409 | norm_num)

private theorem prime_2584487767265781317813 : Nat.Prime 2584487767265781317813 :=
  prime_of_lucas _ 2 [(2, 2), (89, 1), (7259797099061183477, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> first | exact prime_7259797099061183477 | norm_num)

set_option maxRecDepth 4000 in
private theorem prime_64881703735777 : Nat.Prime 64881703735777 :=
  prime_of_lucas _ 5 [(2, 5), (3, 7), (927093389, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> norm_num)

private theorem prime_92691255082156974996979 : Nat.Prime 92691255082156974996979 :=
  prime_of_lucas _ 3 [(2, 1), (3, 1), (31, 1), (467, 1), (16447, 1), (64881703735777, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> first | exact prime_64881703735777 | norm_num)

private theorem prime_43670061551 : Nat.Prime 43670061551 :=
  prime_of_lucas _ 7 [(2, 1), (5, 2), (17, 1), (51376543, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> norm_num)

private theorem prime_13090036741 : Nat.Prime 13090036741 :=
  prime_of_lucas _ 10 [(2, 2), (3, 1), (5, 1), (11, 1), (47, 1), (421987, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> norm_num)

private theorem prime_3819663927398918131021 : Nat.Prime 3819663927398918131021 :=
  prime_of_lucas _ 6 [(2, 2), (3, 2), (5, 1), (19, 1), (113, 1), (755057, 1), (13090036741, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> first | exact prime_13090036741 | norm_num)

private theorem prime_1125266252156850182658904441386709967 :
    Nat.Prime 1125266252156850182658904441386709967 :=
  prime_of_lucas _ 5 [(2, 1), (3373, 1), (43670061551, 1), (3819663927398918131021, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;>
      (first | exact prime_43670061551 | exact prime_3819663927398918131021 | norm_num))

set_option maxRecDepth 4000 in
private theorem prime_15778400344354997994418419698270088123916926905054652752758194827714659 :
    Nat.Prime 15778400344354997994418419698270088123916926905054652752758194827714659 :=
  prime_of_lucas _ 2 [(2, 1), (3, 1), (53, 1), (475709467, 1), (92691255082156974996979, 1),
      (1125266252156850182658904441386709967, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;>
      (first | exact prime_92691255082156974996979 | exact prime_1125266252156850182658904441386709967 | norm_num))

/-- BLS12-381's base field modulus `p` is prime. -/
theorem P_prime : Nat.Prime P :=
  prime_of_lucas _ 2 [(2, 1), (3, 2), (11, 1), (23, 1), (47, 1), (10177, 1), (859267, 1),
      (52437899, 1), (2584487767265781317813, 1),
      (15778400344354997994418419698270088123916926905054652752758194827714659, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;>
      (first | exact prime_2584487767265781317813 | exact prime_15778400344354997994418419698270088123916926905054652752758194827714659 | norm_num))

/-- BLS12-381's group order `r` is prime. -/
theorem R_prime : Nat.Prime R :=
  prime_of_lucas _ 7 [(2, 32), (3, 1), (11, 1), (19, 1), (10177, 1), (125527, 1), (859267, 1),
      (906349, 2), (2508409, 1), (2529403, 1), (52437899, 1), (254760293, 2)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> norm_num)

/-- `ZMod P` is a field: the instance every proof about `Fp` uses. -/
instance fact_P_prime : Fact (Nat.Prime P) := ⟨P_prime⟩

/-- `ZMod R` is a field. -/
instance fact_R_prime : Fact (Nat.Prime R) := ⟨R_prime⟩

/-- `3` does not divide `r`, so cubing is injective on the `r`-th roots of unity. -/
theorem R_coprime_three : Nat.Coprime 3 R := by decide +kernel

end LeanLight.Lc.Bls
