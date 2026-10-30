import LeanLightProofs.Bls.Primes

/-!
# BLS12-381: the large prime factor of the twist cofactor (25c)

The twist curve `E'(𝔽_{p²})` has order `h₂ · r` where the cofactor `h₂` factors as
`13² · 23² · 2713 · 11953 · 262069 · largePrime` with the 448-bit prime `largePrime`
(`largePrime_prime`). As in `LeanLightProofs.Bls.Primes`, each node of the Pratt tree is verified
by Mathlib's `lucas_primality` (`prime_of_lucas`) with `ZMod` powers evaluated directly in the
kernel (`decide +kernel` over `Nat.powMod`), with no `PowMod` helper and no `native_decide`.

Adapted from `EthLib/Cryptography/Proofs/Bls/CofactorPrimes.lean` of
`github.com/ethereum/EthLib` at commit `b4480f4f297301d72f97dfb6ca4ccfa8600fb061`, dedicated to
the public domain under CC0-1.0 (`LeanLightProofs/Vendor/EthLib/LICENSE`).
-/

namespace LeanLight.Lc.Bls

/-! ## `largePrime`'s Pratt tree (EthLib's certificate) -/

private theorem prime_4920833 : Nat.Prime 4920833 :=
  prime_of_lucas _ 3 [(2, 9), (7, 1), (1373, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> norm_num)

private theorem prime_52872661 : Nat.Prime 52872661 :=
  prime_of_lucas _ 2 [(2, 2), (3, 2), (5, 1), (83, 1), (3539, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> norm_num)

private theorem prime_12211063 : Nat.Prime 12211063 :=
  prime_of_lucas _ 5 [(2, 1), (3, 1), (103, 1), (19759, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> norm_num)

private theorem prime_1402724681 : Nat.Prime 1402724681 :=
  prime_of_lucas _ 3 [(2, 3), (5, 1), (7, 1), (1307, 1), (3833, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> norm_num)

private theorem prime_16297965815447 : Nat.Prime 16297965815447 :=
  prime_of_lucas _ 5 [(2, 1), (7, 3), (68059, 1), (349079, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> norm_num)

private theorem prime_810774871 : Nat.Prime 810774871 :=
  prime_of_lucas _ 11 [(2, 1), (3, 1), (5, 1), (89, 1), (151, 1), (2011, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> norm_num)

private theorem prime_63240439939 : Nat.Prime 63240439939 :=
  prime_of_lucas _ 3 [(2, 1), (3, 1), (13, 1), (810774871, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> first | exact prime_810774871 | norm_num)

private theorem prime_1770732318293 : Nat.Prime 1770732318293 :=
  prime_of_lucas _ 2 [(2, 2), (7, 1), (63240439939, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> first | exact prime_63240439939 | norm_num)

private theorem prime_21561538103037546247 : Nat.Prime 21561538103037546247 :=
  prime_of_lucas _ 5 [(2, 1), (3, 3), (225493, 1), (1770732318293, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> first | exact prime_1770732318293 | norm_num)

private theorem prime_86246152412150184989 : Nat.Prime 86246152412150184989 :=
  prime_of_lucas _ 2 [(2, 2), (21561538103037546247, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> first | exact prime_21561538103037546247 | norm_num)

private theorem prime_6716327 : Nat.Prime 6716327 :=
  prime_of_lucas _ 5 [(2, 1), (17, 1), (197539, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> norm_num)

private theorem prime_40297963 : Nat.Prime 40297963 :=
  prime_of_lucas _ 2 [(2, 1), (3, 1), (6716327, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> first | exact prime_6716327 | norm_num)

private theorem prime_241787779 : Nat.Prime 241787779 :=
  prime_of_lucas _ 2 [(2, 1), (3, 1), (40297963, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> first | exact prime_40297963 | norm_num)

private theorem prime_1435735831703 : Nat.Prime 1435735831703 :=
  prime_of_lucas _ 5 [(2, 1), (2969, 1), (241787779, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> first | exact prime_241787779 | norm_num)

private theorem prime_1367711 : Nat.Prime 1367711 :=
  prime_of_lucas _ 7 [(2, 1), (5, 1), (233, 1), (587, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> norm_num)

private theorem prime_12192593745179 : Nat.Prime 12192593745179 :=
  prime_of_lucas _ 2 [(2, 1), (7, 1), (11, 1), (107, 1), (541, 1), (1367711, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> first | exact prime_1367711 | norm_num)

private theorem prime_512088937297519 : Nat.Prime 512088937297519 :=
  prime_of_lucas _ 6 [(2, 1), (3, 1), (7, 1), (12192593745179, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> first | exact prime_12192593745179 | norm_num)

private theorem prime_1857858664515398933 : Nat.Prime 1857858664515398933 :=
  prime_of_lucas _ 2 [(2, 2), (907, 1), (512088937297519, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> first | exact prime_512088937297519 | norm_num)

private theorem prime_22294303974184787197 : Nat.Prime 22294303974184787197 :=
  prime_of_lucas _ 14 [(2, 2), (3, 1), (1857858664515398933, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> first | exact prime_1857858664515398933 | norm_num)

private theorem prime_19931107752921199754119 : Nat.Prime 19931107752921199754119 :=
  prime_of_lucas _ 3 [(2, 1), (3, 1), (149, 1), (22294303974184787197, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;> first | exact prime_22294303974184787197 | norm_num)

private theorem prime_81162125843606155545104998607900118769099783 :
    Nat.Prime 81162125843606155545104998607900118769099783 :=
  prime_of_lucas _ 5 [(2, 1), (3, 2), (2731, 1), (57697, 1), (1435735831703, 1),
      (19931107752921199754119, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;>
      (first | exact prime_1435735831703 | exact prime_19931107752921199754119 | norm_num))

private theorem prime_26935696298915610574513298451669528361624243820491956655650666425177 :
    Nat.Prime 26935696298915610574513298451669528361624243820491956655650666425177 :=
  prime_of_lucas _ 3 [(2, 3), (13, 1), (37, 1), (86246152412150184989, 1),
      (81162125843606155545104998607900118769099783, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;>
      (first | exact prime_86246152412150184989 | exact prime_81162125843606155545104998607900118769099783 | norm_num))

private theorem prime_4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 :
    Nat.Prime 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 :=
  prime_of_lucas _ 3 [(2, 3), (373, 1), (8329, 1), (37501, 1), (661873, 1), (12211063, 1),
      (1402724681, 1), (16297965815447, 1),
      (26935696298915610574513298451669528361624243820491956655650666425177, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;>
      (first
        | exact prime_12211063
        | exact prime_1402724681
        | exact prime_16297965815447
        | exact prime_26935696298915610574513298451669528361624243820491956655650666425177
        | norm_num))

/-- The 448-bit prime factor of the twist cofactor `h₂` of `E'(𝔽_{p²})`. -/
def largePrime : Nat :=
  402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249

/-- `largePrime` is prime. -/
theorem largePrime_prime : Nat.Prime largePrime :=
  prime_of_lucas _ 13 [(2, 4), (3, 1), (11, 1), (631, 1), (4920833, 1), (52872661, 1),
      (4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297, 1)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro f hf; fin_cases hf <;>
      (first
        | exact prime_4920833
        | exact prime_52872661
        | exact prime_4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297
        | norm_num))

theorem prime_13 : Nat.Prime 13 := by norm_num

theorem prime_23 : Nat.Prime 23 := by norm_num

theorem prime_2713 : Nat.Prime 2713 := by norm_num

theorem prime_11953 : Nat.Prime 11953 := by norm_num

theorem prime_262069 : Nat.Prime 262069 := by norm_num

end LeanLight.Lc.Bls
