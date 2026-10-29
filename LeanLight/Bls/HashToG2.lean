import LeanLight.Bls.G2
import LeanLight.Base.Sha256

/-!
# BLS12-381: `hash_to_G2`, RFC 9380's `BLS12381G2_XMD:SHA-256_SSWU_RO_`

Moved from the benchmark's `Bls/HashToG2.lean` (see `LeanLight.Bls.Fp`), with three changes the
specification asks for (`docs/spec-16-light-client.md`, "Cryptography in Lean"):

* **`clear_cofactor` is `[h_eff]P`** (open decision 12), RFC 9380 §7's own definition, where the
  benchmark had Appendix G.3's faster endomorphism chain. It costs about 5 ms more an update.
* **SSWU refuses**: `sswu?` returns `none` when no square root is found for the `y` it needs,
  where the benchmark fell back to zero. For RFC 9380's `Z`, a non-square, `g(x₂) = Z³u⁶·g(x₁)`
  is a square whenever `g(x₁)` is not, so this never happens; a refusal makes the signature
  fail instead of hashing to some other point.
* **The identity is refused**: `hashToG2?` returns `none` when the hash is the identity (also
  never seen; under a signature that is not the identity the pairing check could not pass).

The steps, each RFC 9380's:

1. `expand_message_xmd` with SHA-256 (§5.3.1, §5.3.3 for a DST longer than 255 bytes), to 256
   bytes, `len_in_bytes` for two `Fp2` elements with `L = 64` (`expandXmd`);
2. `hash_to_field`, each 64-byte chunk read big-endian modulo `P` (§5.2, `hashToField`);
3. the simplified SWU map to `E'': y² = x³ + 240u·x + 1012(1 + u)` (§6.6.2, `sswu?`), its
   steps written out plainly, not in constant time (the input is public): Euler's criterion
   picks `x₁` or `x₂`, and `y`'s sign is `u`'s `sgn0`;
4. the 3-isogeny `E'' → E'` (§6.6.3, Appendix E.3, `isoMap`), to Jacobian coordinates without
   an inversion, so that a zero denominator gives the identity, as §6.6.3 requires;
5. the two points added, then `clear_cofactor`.

The isogeny's constants were generated from py_ecc 8.0.0 for the benchmark;
`LeanLightProofs.Bls.Provenance` checks them against EthLib's, which are RFC 9380 E.3's, by the
kernel, and `LeanLightTests.Bls` against the RFC's text, transcribed.

SHA-256 is `LeanLight.Base.Sha256` (ssz-specs', `Ssz.Sha256.hash`), proved equal to `Spec.Sha256.sha256`
(`LeanLightProofs.Sha256.hash_eq_spec`); the benchmark's copy this module first used is gone.
-/

namespace LeanLight.Lc.Bls.H2C

open LeanLight.Lc.Bls

/-- RFC 9380 E.3's `x_num` coefficients `k_(1,0)` to `k_(1,3)`, the constant term first. -/
def isoXNum : Array Fp2 := #[
  ⟨0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6, 0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6⟩,
  ⟨0x0, 0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71a⟩,
  ⟨0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71e, 0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38d⟩,
  ⟨0x171d6541fa38ccfaed6dea691f5fb614cb14b4e7f4e810aa22d6108f142b85757098e38d0f671c7188e2aaaaaaaa5ed1, 0x0⟩]

/-- `x_den`: `k_(2,0)`, `k_(2,1)`, then the monic `x²`'s 1 and a zero `x³`. -/
def isoXDen : Array Fp2 := #[
  ⟨0x0, 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa63⟩,
  ⟨0xc, 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa9f⟩,
  ⟨0x1, 0x0⟩,
  ⟨0x0, 0x0⟩]

/-- `y_num`: `k_(3,0)` to `k_(3,3)`. -/
def isoYNum : Array Fp2 := #[
  ⟨0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706, 0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706⟩,
  ⟨0x0, 0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97be⟩,
  ⟨0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71c, 0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38f⟩,
  ⟨0x124c9ad43b6cf79bfbf7043de3811ad0761b0f37a1e26286b0e977c69aa274524e79097a56dc4bd9e1b371c71c718b10, 0x0⟩]

/-- `y_den`: `k_(4,0)` to `k_(4,2)`, then the monic `x³`'s 1. -/
def isoYDen : Array Fp2 := #[
  ⟨0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb, 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb⟩,
  ⟨0x0, 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa9d3⟩,
  ⟨0x12, 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa99⟩,
  ⟨0x1, 0x0⟩]

/-- `A' = 240·u`. -/
def sswuA : Fp2 := ⟨0x0, 0xf0⟩
/-- `B' = 1012·(1 + u)`. -/
def sswuB : Fp2 := ⟨0x3f4, 0x3f4⟩
/-- `Z = −(2 + u)`. -/
def sswuZ : Fp2 :=
  ⟨0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaa9,
   0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa⟩

theorem sswuZ_eq : sswuZ = (⟨2, 1⟩ : Fp2).neg := by decide

/-- 64 zero bytes, `Z_pad`. -/
def zPad : ByteArray := natBe 0 64

/-- `expand_message_xmd(msg, dst, 256)` with SHA-256 (RFC 9380 §5.3.1): `ell = 8` blocks
`b₁ … b₈`, with `b₀ = H(Z_pad ‖ msg ‖ I2OSP(256, 2) ‖ I2OSP(0, 1) ‖ DST')` and
`bᵢ = H((b₀ ⊕ bᵢ₋₁) ‖ I2OSP(i, 1) ‖ DST')`, `DST' = DST ‖ I2OSP(len(DST), 1)`; a DST longer than
255 bytes is first replaced by `H("H2C-OVERSIZE-DST-" ‖ DST)` (§5.3.3). -/
def expandXmd (msg dst : ByteArray) : ByteArray := Id.run do
  let dst := if dst.size > 255 then Ssz.Sha256.hash ("H2C-OVERSIZE-DST-".toUTF8 ++ dst) else dst
  let dstPrime := dst.push dst.size.toUInt8
  let b0 := Ssz.Sha256.hash (zPad ++ msg ++ ByteArray.mk #[1, 0, 0] ++ dstPrime)
  let mut bi := Ssz.Sha256.hash (b0.push 1 ++ dstPrime)
  let mut out := bi
  for i in [2:9] do
    let mut x := ByteArray.empty
    for j in [0:32] do
      x := x.push ((b0[j]?.getD 0) ^^^ (bi[j]?.getD 0))
    bi := Ssz.Sha256.hash (x.push i.toUInt8 ++ dstPrime)
    out := out ++ bi
  return out

/-- `hash_to_field(msg, 2)` for `Fp2` with `L = 64`: four 64-byte chunks of `expandXmd`, each
read big-endian modulo `P`. -/
def hashToField (msg dst : ByteArray) : Fp2 × Fp2 :=
  let u := expandXmd msg dst
  let e (k : Nat) := beNat u (64 * k) 64 % P
  (⟨e 0, e 1⟩, ⟨e 2, e 3⟩)

/-- `g(x) = x³ + A'x + B'`, the right side of `E''`. -/
@[inline] def gIso (x : Fp2) : Fp2 := (x.sqr.add sswuA).mul x |>.add sswuB

/-- The simplified SWU map to `E''` (RFC 9380 §6.6.2): `x₁ = (−B'/A')(1 + 1/(Z²u⁴ + Zu²))`, or
`B'/(ZA')` when that denominator is zero; `x₁` if `g(x₁)` is a square, else `x₂ = Zu²x₁`; `y`
the root of `g(x)` whose `sgn0` is `u`'s. `none` when no root is found (never, for this `Z`). -/
def sswu? (u : Fp2) : Option G2A :=
  let zu2 := sswuZ.mul u.sqr
  let tv := zu2.sqr.add zu2
  let x1 :=
    if tv.isZero then sswuB.mul (sswuZ.mul sswuA).inv
    else (sswuB.neg.mul sswuA.inv).mul (Fp2.one.add tv.inv)
  let gx1 := gIso x1
  let (x, gx) := if gx1.isSquare then (x1, gx1) else let x2 := zu2.mul x1; (x2, gIso x2)
  match gx.sqrt? with
  | none => none
  | some y => some ⟨x, if u.sgn0 == y.sgn0 then y else y.neg⟩

/-- `Σ ks[i]·x^i` by Horner's rule. -/
def horner (ks : Array Fp2) (x : Fp2) : Fp2 := Id.run do
  let mut acc := Fp2.zero
  for k in [0:ks.size] do
    acc := (acc.mul x).add (ks[ks.size - 1 - k]?.getD Fp2.zero)
  return acc

/-- The 3-isogeny `E'' → E'` (RFC 9380 Appendix E.3), `(x_num/x_den, y·y_num/y_den)`, to Jacobian
coordinates without an inversion: `Z = x_den·y_den`, `X = x_num·x_den·y_den²`,
`Y = y·y_num·x_den³·y_den²`. A zero denominator gives `Z = 0`, the identity. -/
def isoMap (p : G2A) : G2J :=
  let xn := horner isoXNum p.x
  let xd := horner isoXDen p.x
  let yn := horner isoYNum p.x
  let yd := horner isoYDen p.x
  let yd2 := yd.sqr
  ⟨(xn.mul xd).mul yd2, ((p.y.mul yn).mul (xd.sqr.mul xd)).mul yd2, xd.mul yd⟩

/-- `clear_cofactor(P) = [h_eff]P` (RFC 9380 §7, open decision 12). -/
def clearCofactor (p : G2J) : G2J :=
  match p.toAffine? with
  | some a => G2J.mulA a hEff
  | none => G2J.inf

/-- `hash_to_curve(msg)` for G2 under `dst`, affine; `none` when SSWU refuses or the result is
the identity. -/
def hashToG2? (msg dst : ByteArray) : Option G2A :=
  let (u0, u1) := hashToField msg dst
  match sswu? u0, sswu? u1 with
  | some q0, some q1 => (clearCofactor ((isoMap q0).add (isoMap q1))).toAffine?
  | _, _ => none

end LeanLight.Lc.Bls.H2C
