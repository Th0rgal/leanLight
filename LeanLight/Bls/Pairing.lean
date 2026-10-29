import LeanLight.Bls.Fp12
import LeanLight.Bls.G1
import LeanLight.Bls.G2

/-!
# BLS12-381: the optimal ate pairing, as a check that a product of pairings is one

Moved from the benchmark's `Bls/Pairing.lean` (see `LeanLight.Bls.Fp`).

**The Miller loop** (`millerLoop`) runs over `|x| = 0xd201000000010000` for every pair at once,
with one accumulator in `Fp12`: each G2 point in Jacobian coordinates, the lines evaluated
sparsely (Costello–Lange–Naehrig, eprint 2010/354, algorithms 26 and 27, as zkcrypto/bls12_381
adapts them), and the result conjugated at the end since `x < 0`. Its pairs exclude the
identity; the callers refuse it before (`LeanLight.Bls.Fav`).

**The final exponentiation** (`finalExp`): the easy part `(p⁶ − 1)(p² + 1)` by a conjugation, an
inversion and the Frobenius, the hard part by zkcrypto's chain of five exponentiations by `x`
with Granger–Scott cyclotomic squarings. **It computes the cube** of the final exponentiation:
`finalExp f = (f^((p¹² − 1)/r))³`, where EthLib's `finalExponentiation` is
`f^((p¹² − 1)/r)` itself. A check that a product of pairings is one loses nothing by it: the
value lies in the `r`-th roots of unity and `gcd(3, r) = 1`, so its cube is one exactly when it
is (the cube lemma, LC4b). `LeanLightTests.Bls` checks the cube against EthLib's naive power on Miller
loops of several pairs.

**The check** (`pairingCheck`): `∏ e(pᵢ, qᵢ) = 1` with one Miller loop and one final
exponentiation over all the pairs.
-/

namespace LeanLight.Lc.Bls

/-- Doubling step: `2T` and the tangent line's coefficients. -/
def dblStep (r : G2J) : G2J × Fp2 × Fp2 × Fp2 :=
  let tmp0 := r.x.sqr
  let tmp1 := r.y.sqr
  let tmp2 := tmp1.sqr
  let tmp3 := ((tmp1.add r.x).sqr.sub tmp0 |>.sub tmp2).dbl
  let tmp4 := tmp0.dbl.add tmp0
  let tmp6 := r.x.add tmp4
  let tmp5 := tmp4.sqr
  let zsq := r.z.sqr
  let x3 := (tmp5.sub tmp3).sub tmp3
  let z3 := ((r.z.add r.y).sqr.sub tmp1).sub zsq
  let y3 := ((tmp3.sub x3).mul tmp4).sub tmp2.dbl.dbl.dbl
  let t3 := (tmp4.mul zsq).dbl.neg
  let t6 := ((tmp6.sqr.sub tmp0).sub tmp5).sub tmp1.dbl.dbl
  let t0 := (z3.mul zsq).dbl
  (⟨x3, y3, z3⟩, t0, t3, t6)

/-- Addition step: `T + Q` (`Q` affine) and the chord's coefficients. -/
def addStep (r : G2J) (q : G2A) : G2J × Fp2 × Fp2 × Fp2 :=
  let zsq := r.z.sqr
  let ysq := q.y.sqr
  let t0 := zsq.mul q.x
  let t1 := (((q.y.add r.z).sqr.sub ysq).sub zsq).mul zsq
  let t2 := t0.sub r.x
  let t3 := t2.sqr
  let t4 := t3.dbl.dbl
  let t5 := t4.mul t2
  let t6 := (t1.sub r.y).sub r.y
  let t9 := t6.mul q.x
  let t7 := t4.mul r.x
  let x3 := ((t6.sqr.sub t5).sub t7).sub t7
  let z3 := ((r.z.add t2).sqr.sub zsq).sub t3
  let t10 := q.y.add z3
  let t8 := (t7.sub x3).mul t6
  let t0' := (r.y.mul t5).dbl
  let y3 := t8.sub t0'
  let t10' := (t10.sqr.sub ysq).sub z3.sqr
  let t9' := t9.dbl.sub t10'
  let t10'' := z3.dbl
  let t1' := t6.neg.dbl
  (⟨x3, y3, z3⟩, t10'', t1', t9')

/-- Multiplies `f` by the line `(c0, c1, c2)` evaluated at `p`. -/
@[inline] def ell (f : Fp12) (c0 c1 c2 : Fp2) (p : G1A) : Fp12 :=
  f.mulBy014 c2 (c1.mulFp p.x) (c0.mulFp p.y)

/-- The Miller loop of `∏ e(pᵢ, qᵢ)`, before the final exponentiation, over pairs that are not
the identity. -/
def millerLoop (ps : List (G1A × G2A)) : Fp12 := Id.run do
  let mut f := Fp12.one
  let mut ts : List G2J := ps.map fun pq => G2J.ofAffine pq.2
  for k in [0:63] do
    let i := 62 - k
    if k ≠ 0 then f := f.sqr
    let mut acc : List G2J := []
    for (t, pq) in ts.zip ps do
      let (t', c0, c1, c2) := dblStep t
      f := ell f c0 c1 c2 pq.1
      acc := t' :: acc
    ts := acc.reverse
    if (X >>> i) % 2 = 1 then
      let mut acc2 : List G2J := []
      for (t, pq) in ts.zip ps do
        let (t', c0, c1, c2) := addStep t pq.2
        f := ell f c0 c1 c2 pq.1
        acc2 := t' :: acc2
      ts := acc2.reverse
  return f.conj

/-- `(a + b·y)²` in `Fp4 = Fp2[y]/(y² − ξ)`, for the cyclotomic squaring. -/
@[inline] def fp4Sqr (a b : Fp2) : Fp2 × Fp2 :=
  let t0 := a.sqr
  let t1 := b.sqr
  (t1.mulXi.add t0, ((a.add b).sqr.sub t0).sub t1)

/-- Granger–Scott squaring in the cyclotomic subgroup (eprint 2009/565). -/
def cycSqr (f : Fp12) : Fp12 :=
  let z0 := f.c0.c0
  let z4 := f.c0.c1
  let z3 := f.c0.c2
  let z2 := f.c1.c0
  let z1 := f.c1.c1
  let z5 := f.c1.c2
  let (t0, t1) := fp4Sqr z0 z1
  let z0 := (t0.sub z0).dbl.add t0
  let z1 := (t1.add z1).dbl.add t1
  let (t0, t1) := fp4Sqr z2 z3
  let (t2, t3) := fp4Sqr z4 z5
  let z4 := (t0.sub z4).dbl.add t0
  let z5 := (t1.add z5).dbl.add t1
  let t0 := t3.mulXi
  let z2 := (t0.add z2).dbl.add t0
  let z3 := (t2.sub z3).dbl.add t2
  ⟨⟨z0, z4, z3⟩, ⟨z2, z1, z5⟩⟩

/-- `f^x` for `f` in the cyclotomic subgroup (`x` negative: conjugated). -/
def cycExpX (f : Fp12) : Fp12 := Id.run do
  let mut tmp := Fp12.one
  let mut found := false
  for k in [0:64] do
    let bit := (X >>> (63 - k)) % 2 = 1
    if found then tmp := cycSqr tmp else found := bit
    if bit then tmp := tmp.mul f
  return tmp.conj

/-- The cube of the final exponentiation, `f^(3(p¹² − 1)/r)` (zkcrypto's chain). -/
def finalExp (f : Fp12) : Fp12 :=
  let t0 := f.conj
  let t1 := f.inv
  let t2 := t0.mul t1
  let t1 := t2
  let t2 := t2.frob.frob.mul t1
  let t1 := (cycSqr t2).conj
  let t3 := cycExpX t2
  let t4 := cycSqr t3
  let t5 := t1.mul t3
  let t1 := cycExpX t5
  let t0 := cycExpX t1
  let t6 := cycExpX t0
  let t6 := t6.mul t4
  let t4 := cycExpX t6
  let t5 := t5.conj
  let t4 := t4.mul (t5.mul t2)
  let t5 := t2.conj
  let t1 := t1.mul t2
  let t1 := t1.frob.frob.frob
  let t6 := t6.mul t5
  let t6 := t6.frob
  let t3 := t3.mul t0
  let t3 := t3.frob.frob
  let t3 := t3.mul t1
  let t3 := t3.mul t6
  t3.mul t4

/-- `∏ e(pᵢ, qᵢ) = 1`, with one Miller loop and one final exponentiation, over pairs that are
not the identity. -/
def pairingCheck (ps : List (G1A × G2A)) : Bool := (finalExp (millerLoop ps)).isOne

end LeanLight.Lc.Bls
