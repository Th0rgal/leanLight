import LeanLight.Bls.Fav
import LeanLightProofs.Vendor.EthLib.Bls.Signatures
import LeanLightTests.Bls.Util
import LeanLightTests.Bls.Vectors

/-!
# Where the hash-to-curve constants come from

The 3-isogeny's constants of the runtime layer (`LeanLight.Bls.H2C`, generated from py_ecc 8.0.0
for the benchmark) and of EthLib's (`k10` to `k42`, "reproduced verbatim from the RFC") are
compared with RFC 9380 Appendix E.3's text, transcribed by `scripts/bls-vectors.py` from the
RFC's `.txt` (`Vectors.rfcE3`), and with py_ecc's (`Vectors.pyEccIso`); so are `h_eff`
(§8.8.2), SSWU's `A'`, `B'` and `Z`, and Ethereum's DST. `LeanLightProofs.Bls.Provenance` checks
the runtime's against EthLib's by the kernel too.
-/

namespace LeanLight.Tests.Bls

open Vectors

def provenance : Tally := Id.run do
  let mut t : Tally := {}
  let rt : List ((Nat × Nat) × Nat × Nat) := Id.run do
    let mut out := []
    for (i, ks) in [(1, LeanLight.Lc.Bls.H2C.isoXNum), (2, LeanLight.Lc.Bls.H2C.isoXDen),
        (3, LeanLight.Lc.Bls.H2C.isoYNum), (4, LeanLight.Lc.Bls.H2C.isoYDen)] do
      for j in [0:ks.size] do
        let k := ks[j]?.getD LeanLight.Lc.Bls.Fp2.zero
        out := out ++ [((i, j), k.c0, k.c1)]
    return out
  let num (l : List ((Nat × Nat) × String × String)) :=
    l.map fun (ij, a, b) => (ij, natOfHex a, natOfHex b)
  let rfcK := num rfcE3
  let pyK := num pyEccIso
  -- Every RFC constant is the runtime's and py_ecc's, at the same place.
  for (ij, a, b) in rfcK do
    t := t.add s!"k_{ij}: runtime = RFC 9380 E.3" (rt.contains (ij, a, b))
    t := t.add s!"k_{ij}: py_ecc = RFC 9380 E.3" (pyK.contains (ij, a, b))
  -- The runtime's other coefficients are the monic denominators' 1 and x_den's zero x³.
  t := t.add "runtime's coefficients beyond E.3: x_den's x² and y_den's x³ are 1, x_den's x³ 0"
    ((rt.filter fun (ij, _) => !(rfcK.any (·.1 == ij))) ==
      [((2, 2), 1, 0), ((2, 3), 0, 0), ((4, 3), 1, 0)])
  let eth : List ((Nat × Nat) × EthLib.Cryptography.Bls.Fp2) :=
    open EthLib.Cryptography.Bls.HashToCurve in
    [((1, 0), k10), ((1, 1), k11), ((1, 2), k12), ((1, 3), k13), ((2, 0), k20), ((2, 1), k21),
     ((3, 0), k30), ((3, 1), k31), ((3, 2), k32), ((3, 3), k33), ((4, 0), k40), ((4, 1), k41),
     ((4, 2), k42)]
  t := t.add "EthLib's k10 to k42 = RFC 9380 E.3"
    (eth.map (fun (ij, k) => (ij, k.c0.val, k.c1.val)) == rfcK)
  t := t.add "h_eff: runtime = EthLib (vendored) = RFC 9380 §8.8.2"
    (LeanLight.Lc.Bls.hEff == natOfHex rfcHEff &&
      EthLib.Cryptography.Bls.HashToCurve.hEff == natOfHex rfcHEff)
  let fp2 (a : EthLib.Cryptography.Bls.Fp2) : LeanLight.Lc.Bls.Fp2 := ⟨a.c0.val, a.c1.val⟩
  t := t.add "SSWU's A' = 240 I, B' = 1012 (1 + I), Z = -(2 + I): runtime = EthLib"
    (LeanLight.Lc.Bls.H2C.sswuA == ⟨0, 240⟩ && LeanLight.Lc.Bls.H2C.sswuB == ⟨1012, 1012⟩ &&
      LeanLight.Lc.Bls.H2C.sswuZ == ⟨LeanLight.Lc.Bls.P - 2, LeanLight.Lc.Bls.P - 1⟩ &&
      fp2 EthLib.Cryptography.Bls.HashToCurve.Aprime == LeanLight.Lc.Bls.H2C.sswuA &&
      fp2 EthLib.Cryptography.Bls.HashToCurve.Bprime == LeanLight.Lc.Bls.H2C.sswuB &&
      fp2 EthLib.Cryptography.Bls.HashToCurve.Z == LeanLight.Lc.Bls.H2C.sswuZ)
  t := t.add "Ethereum's DST: runtime = EthLib"
    (LeanLight.Lc.Bls.ethDst == EthLib.Cryptography.Bls.Signatures.DST &&
      LeanLight.Lc.Bls.ethDst == "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_".toUTF8)
  return t

end LeanLight.Tests.Bls
