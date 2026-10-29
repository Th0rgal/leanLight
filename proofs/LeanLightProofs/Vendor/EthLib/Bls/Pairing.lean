import LeanLightProofs.Vendor.EthLib.Bls.G1
import LeanLightProofs.Vendor.EthLib.Bls.G2
import LeanLightProofs.Vendor.EthLib.Bls.Fp12

/-!
# BLS12-381, readable layer: `Pairing`

Derived from `EthLib/Cryptography/Bls/Pairing.lean` of github.com/ethereum/EthLib at commit
`57af539e81b8c6f0f54c8b4da3adbc77b122a100`, which its authors dedicated to the public domain
under CC0-1.0 (`LeanLightProofs/Vendor/EthLib/LICENSE`). Rewritten to the Runtime Lean rules:
`partial` definitions take fuel or recurse structurally, `a[i]!` is `a[i]?.getD 0`, panics return
`Except`, `while` loops are bounded `for` loops. `millerLoop` is no longer `partial`: its two `while` loops are `Nat.log2` (the number of bits of `s`, which the first counted) and a `for` loop over the same indices `highBit − 2` down to 0. No semantic change.

It is the specification `LeanLight.Bls` is to be proved equal to (`docs/spec-16-light-client.md`,
invariant 25c, LC4b), not code the wallet runs; it imports nothing beyond Lean core, so
`tests` compiles it into the test executable that runs both layers on the vectors. Its
imports and its namespace are EthLib's, the module paths moved under `LeanLightProofs.Vendor.EthLib`.
-/

/-!
# `Pairing`

The optimal-ate pairing for BLS12-381:

  e(P, Q) = Miller(|x|, Q', P')^((p¹² − 1) / r)

where:
  * `x = -0xD201_0000_0001_0000` is the BLS curve parameter (negative).
  * `P` ∈ G1, `Q` ∈ G2.
  * `Q'` ∈ E(Fp12) is the untwisted image of Q.
  * `P'` ∈ E(Fp12) is the trivial Fp ↪ Fp12 inclusion of P.

`Miller(s, R, T)` accumulates a value in Fp12 by walking the bits of
`s`: at each step it doubles `R` (and multiplies the running product by
the tangent line at the old `R`, evaluated at `T`); when a bit is set,
it also adds the original input `R₀` to `R` (multiplying by the line
through them, again evaluated at `T`).

For BLS curves with negative `x`, the final result is then conjugated.

The final exponentiation reduces the Miller output to the `r`-th roots
of unity in `Fp12*`, where the bilinear pairing actually lives.
-/

namespace EthLib.Cryptography.Bls

/-! ## Embedding G1 and G2 into E(Fp12)

To compute the Miller loop over `Fp12` we lift both groups to a single
ambient curve `E : y² = x³ + 4` over `Fp12`.

* G1's coordinates are already in `Fp ⊂ Fp12`. Just wrap them.
* G2's coordinates live on the twist `E' : y² = x³ + 4·(1+i)` over `Fp2`.
  The untwist isomorphism sends `(X, Y) ↦ (X / w², Y / w³)`, where
  `w ∈ Fp12` is the generator with `w² = v ∈ Fp6` and `v³ = 1+i ∈ Fp2`.
  We compute `w⁻²` and `w⁻³` once at the start of a pairing.
-/

namespace Embedded

/-- An affine point on `E/Fp12`. -/
structure Point where
  x : Fp12
  y : Fp12
  inf : Bool := false
deriving Inhabited

/-- Lift a `G1` point into `E(Fp12)` via the trivial inclusion. -/
def ofG1 (p : G1) : Point :=
  if p.isInfinity then { x := Fp12.zero, y := Fp12.zero, inf := true }
  else
    let (xp, yp) := p.toAffine
    { x := ⟨Fp6.ofFp2 (Fp2.ofFp xp), Fp6.zero⟩
    , y := ⟨Fp6.ofFp2 (Fp2.ofFp yp), Fp6.zero⟩ }

/-- `w⁻² ∈ Fp12`. Since `w² = v ∈ Fp6`, this is `v⁻¹` lifted. -/
def wInv2 : Fp12 :=
  let v : Fp6 := ⟨Fp2.zero, Fp2.one, Fp2.zero⟩
  ⟨v.inverse, Fp6.zero⟩

/-- `w⁻³ ∈ Fp12`, equal to `v⁻²·w` in `⟨c0, c1⟩` form. -/
def wInv3 : Fp12 :=
  let v : Fp6 := ⟨Fp2.zero, Fp2.one, Fp2.zero⟩
  let v2inv := (v * v).inverse
  ⟨Fp6.zero, v2inv⟩

/-- Lift a `G2` point into `E(Fp12)` via the untwist isomorphism
`(X, Y) ↦ (X / w², Y / w³)`. -/
def ofG2 (p : G2) : Point :=
  if p.isInfinity then { x := Fp12.zero, y := Fp12.zero, inf := true }
  else
    let (X, Y) := p.toAffine
    let X12 : Fp12 := ⟨Fp6.ofFp2 X, Fp6.zero⟩
    let Y12 : Fp12 := ⟨Fp6.ofFp2 Y, Fp6.zero⟩
    { x := X12 * wInv2, y := Y12 * wInv3 }

end Embedded

/-! ## Line functions -/

namespace Line

/-- Slope of the line through two distinct points. -/
@[inline] def addSlope (Rx Ry Tx Ty : Fp12) : Fp12 :=
  (Ty - Ry) * (Tx - Rx).inverse

/-- Slope of the tangent at `R`. -/
@[inline] def tangentSlope (Rx Ry : Fp12) : Fp12 :=
  let three : Fp12 := ⟨Fp6.ofFp2 (Fp2.ofFp (Fp.ofNat 3)), Fp6.zero⟩
  let two   : Fp12 := ⟨Fp6.ofFp2 (Fp2.ofFp (Fp.ofNat 2)), Fp6.zero⟩
  three * Rx * Rx * (two * Ry).inverse

/-- Evaluate the line at `(xp, yp)`: `(yp − Ry) − slope·(xp − Rx)`. -/
@[inline] def evalAt (Rx Ry slope xp yp : Fp12) : Fp12 :=
  (yp - Ry) - slope * (xp - Rx)

end Line

/-! ## Miller loop -/

/-- Doubling step: `(T, f) ↦ (2T, f² · l_{T,T}(P))`. -/
def millerDouble (T : Embedded.Point) (P : Embedded.Point) (f : Fp12)
    : Embedded.Point × Fp12 :=
  if T.inf then (T, f * f)
  else
    let m := Line.tangentSlope T.x T.y
    let nx := m * m - T.x - T.x
    let ny := m * (T.x - nx) - T.y
    let line := Line.evalAt T.x T.y m P.x P.y
    ({ x := nx, y := ny, inf := false }, f * f * line)

/-- Addition step: `(T, f) ↦ (T + R₀, f · l_{T,R₀}(P))`. -/
def millerAdd (T R₀ : Embedded.Point) (P : Embedded.Point) (f : Fp12)
    : Embedded.Point × Fp12 :=
  if T.inf then (R₀, f)
  else if R₀.inf then (T, f)
  else
    let m := Line.addSlope T.x T.y R₀.x R₀.y
    let nx := m * m - T.x - R₀.x
    let ny := m * (T.x - nx) - T.y
    let line := Line.evalAt T.x T.y m P.x P.y
    ({ x := nx, y := ny, inf := false }, f * line)

/-- Walk the bits of `s` from the most-significant down. -/
def millerLoop (s : Nat) (R₀ P : Embedded.Point) : Fp12 := Id.run do
  if s = 0 then return Fp12.one
  -- The number of bits of `s` (EthLib counted them with a `while` loop).
  let highBit := s.log2 + 1
  -- Iterate from highBit-2 down to 0 (the leading bit is consumed by
  -- the initial T = R₀ and f = 1).
  let mut T := R₀
  let mut f := Fp12.one
  for k in [0:highBit - 1] do
    let i := highBit - 2 - k
    let (T', f') := millerDouble T P f
    T := T'; f := f'
    if (s >>> i) &&& 1 = 1 then
      let (T'', f'') := millerAdd T R₀ P f
      T := T''; f := f''
  return f

/-! ## Final exponentiation -/

/-- The exponent `(p¹² − 1) / r`. -/
def finalExpExponent : Nat :=
  (Fp.modulus ^ 12 - 1) / Fr.modulus

/-- Raise `f` to `(p¹² − 1) / r`. -/
@[inline] def finalExponentiation (f : Fp12) : Fp12 :=
  Fp12.powNat f finalExpExponent

/-! ## The pairing -/

/-- The BLS parameter `|x|`. -/
def blsX : Nat := 0xD201000000010000

/-- Returns `true` iff `∏ e(P_i, Q_i) = 1`. -/
def pairingCheck (pairs : Array (G1 × G2)) : Bool := Id.run do
  let mut acc : Fp12 := Fp12.one
  for (p, q) in pairs do
    -- Identity pairs contribute 1.
    if p.isInfinity || q.isInfinity then continue
    let f := millerLoop blsX (Embedded.ofG2 q) (Embedded.ofG1 p)
    acc := acc * f.conjugate
  return (finalExponentiation acc).isOne

end EthLib.Cryptography.Bls
