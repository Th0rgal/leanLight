import LeanLightProofs.Vendor.EthLib.Bls.Signatures
import LeanLightTests.Bls.Layer

/-!
# EthLib's readable layer under test

`readable` is the `Layer` over EthLib's code as vendored in `LeanLightProofs.Vendor.EthLib.Bls`:
its own `ethFastAggregateVerify`, `fastAggregateVerify` and `ethAggregatePubkeys`, and its
decompression with `inSubgroup` for the deserialization vectors.
-/

namespace LeanLight.Tests.Bls

open EthLib.Cryptography.Bls

/-- An affine point of EthLib's G2, unless it is the identity. -/
def ethPt2 (p : G2) : Option Pt2 :=
  if p.isInfinity then none
  else let (x, y) := p.toAffine; some (x.c0.val, x.c1.val, y.c0.val, y.c1.val)

/-- EthLib's layer. -/
def readable : Layer where
  name := "readable"
  fav pks msg sig := Signatures.fastAggregateVerify pks.toArray msg sig
  ethFav pks msg sig := Signatures.ethFastAggregateVerify pks.toArray msg sig
  ethAgg pks := match Signatures.ethAggregatePubkeys pks.toArray with
    | .ok b => some b
    | .error _ => none
  deserG1 b := match G1.uncompress b with
    | .ok p => G1.inSubgroup p
    | .error _ => false
  deserG2 b := match G2.uncompress b with
    | .ok p => G2.inSubgroup p
    | .error _ => false
  sign sk msg :=
    if sk = 0 || sk ≥ Fr.modulus then none
    else match HashToCurve.hashToG2 msg Signatures.DST with
      | .ok h => some (G2.compress (G2.mulNat h sk))
      | .error _ => none
  h2g msg dst := match HashToCurve.hashToG2 msg dst with
    | .ok p => ethPt2 p
    | .error _ => none
  h2f msg dst := match HashToCurve.hashToFieldFp2 msg dst 2 with
    | .ok us =>
      let u0 := us[0]?.getD Fp2.zero
      let u1 := us[1]?.getD Fp2.zero
      some ((u0.c0.val, u0.c1.val), (u1.c0.val, u1.c1.val))
    | .error _ => none
  map u := match HashToCurve.simpleSwu ⟨Fp.ofNat u.1, Fp.ofNat u.2⟩ with
    | .ok (x, y) => ethPt2 (HashToCurve.isoMapG2 x y)
    | .error _ => none
  sha256 := Ssz.Sha256.hash

end LeanLight.Tests.Bls
