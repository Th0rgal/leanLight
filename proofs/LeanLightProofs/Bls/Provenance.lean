import LeanLight.Bls.Fav
import LeanLightProofs.Vendor.EthLib.Bls.Signatures

/-!
# The runtime layer's constants are EthLib's

Each constant `LeanLight.Bls` pins is the one EthLib's readable layer
(`LeanLightProofs.Vendor.EthLib.Bls`) names, by the kernel: the moduli `p` and `r`, `|x|`, `h_eff`,
the generators, the twist's `b`, and the hash-to-curve constants of RFC 9380 (SSWU's `A'`, `B'`
and `Z`, Appendix E.3's isogeny coefficients, which the runtime took from py_ecc 8.0.0 and
EthLib "reproduced verbatim from the RFC"; `docs/spec-16-light-client.md`, "Sources", C4c). The
test executable (`tests`, `LeanLightTests.Bls.Provenance`) compares both with the RFC's text
and with py_ecc. These are checks of data, not 25c, whose theorems are LC4b's.
-/

namespace LeanLight.Lc.Bls.Provenance

open EthLib.Cryptography.Bls
open EthLib.Cryptography.Bls.HashToCurve (k10 k11 k12 k13 k20 k21 k30 k31 k32 k33 k40 k41 k42)

/-- EthLib's `Fp2`, as the runtime's pair of `Nat`s. -/
def ofEth (a : EthLib.Cryptography.Bls.Fp2) : LeanLight.Lc.Bls.Fp2 := ⟨a.c0.val, a.c1.val⟩

theorem P_eq : LeanLight.Lc.Bls.P = Fp.modulus := by decide +kernel
theorem R_eq : LeanLight.Lc.Bls.R = Fr.modulus := by decide +kernel
theorem X_eq : LeanLight.Lc.Bls.X = blsX := by decide +kernel
theorem hEff_eq : LeanLight.Lc.Bls.hEff = HashToCurve.hEff := by decide +kernel

theorem g1Gen_eq :
    (LeanLight.Lc.Bls.g1Gen.x, LeanLight.Lc.Bls.g1Gen.y) = (G1.generator.x.val, G1.generator.y.val) := by
  decide +kernel

theorem g2Gen_eq :
    (LeanLight.Lc.Bls.g2Gen.x, LeanLight.Lc.Bls.g2Gen.y) = (ofEth G2.generator.x, ofEth G2.generator.y) := by
  decide +kernel

theorem bTwist_eq : LeanLight.Lc.Bls.bTwist = ofEth G2.bTwist := by decide +kernel

theorem sswu_eq :
    H2C.sswuA = ofEth HashToCurve.Aprime ∧ H2C.sswuB = ofEth HashToCurve.Bprime ∧
      H2C.sswuZ = ofEth HashToCurve.Z := by
  decide +kernel

theorem isoXNum_eq : H2C.isoXNum = #[ofEth k10, ofEth k11, ofEth k12, ofEth k13] := by
  decide +kernel

/-- `x_den`'s coefficients beyond E.3's are the monic `x²`'s 1 and a zero `x³`. -/
theorem isoXDen_eq : H2C.isoXDen = #[ofEth k20, ofEth k21, ⟨1, 0⟩, ⟨0, 0⟩] := by
  decide +kernel

theorem isoYNum_eq : H2C.isoYNum = #[ofEth k30, ofEth k31, ofEth k32, ofEth k33] := by
  decide +kernel

/-- `y_den`'s coefficient beyond E.3's is the monic `x³`'s 1. -/
theorem isoYDen_eq : H2C.isoYDen = #[ofEth k40, ofEth k41, ofEth k42, ⟨1, 0⟩] := by
  decide +kernel

end LeanLight.Lc.Bls.Provenance
