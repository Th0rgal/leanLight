import LeanLight.Bls.Fp2

/-!
# BLS12-381: `Fp6 = Fp2[v]/(v³ − ξ)`, `ξ = 1 + u`

Moved from the benchmark's `Bls/Field.lean` (see `LeanLight.Bls.Fp`). Multiplication interpolates
with six `Fp2` multiplications, squaring is Chung–Hasan's SQR2, and `mulBy1` and `mulBy01` are
zkcrypto/bls12_381's sparse products for the Miller loop's lines.
-/

namespace LeanLight.Lc.Bls

/-- `c0 + c1·v + c2·v²`. -/
structure Fp6 where
  c0 : Fp2
  c1 : Fp2
  c2 : Fp2
deriving DecidableEq

namespace Fp6

@[inline] def zero : Fp6 := ⟨Fp2.zero, Fp2.zero, Fp2.zero⟩
@[inline] def one : Fp6 := ⟨Fp2.one, Fp2.zero, Fp2.zero⟩
@[inline] def add (a b : Fp6) : Fp6 := ⟨a.c0.add b.c0, a.c1.add b.c1, a.c2.add b.c2⟩
@[inline] def sub (a b : Fp6) : Fp6 := ⟨a.c0.sub b.c0, a.c1.sub b.c1, a.c2.sub b.c2⟩
@[inline] def neg (a : Fp6) : Fp6 := ⟨a.c0.neg, a.c1.neg, a.c2.neg⟩
@[inline] def dbl (a : Fp6) : Fp6 := ⟨a.c0.dbl, a.c1.dbl, a.c2.dbl⟩
@[inline] def eq (a b : Fp6) : Bool := a.c0.eq b.c0 && a.c1.eq b.c1 && a.c2.eq b.c2
@[inline] def isZero (a : Fp6) : Bool := a.c0.isZero && a.c1.isZero && a.c2.isZero

/-- Six `Fp2` multiplications (Karatsuba-style interpolation). -/
def mul (a b : Fp6) : Fp6 :=
  let aa := a.c0.mul b.c0
  let bb := a.c1.mul b.c1
  let cc := a.c2.mul b.c2
  let t1 := (((a.c1.add a.c2).mul (b.c1.add b.c2)).sub bb |>.sub cc).mulXi.add aa
  let t3 := ((a.c0.add a.c2).mul (b.c0.add b.c2)).sub aa |>.add bb |>.sub cc
  let t2 := ((a.c0.add a.c1).mul (b.c0.add b.c1)).sub aa |>.sub bb |>.add cc.mulXi
  ⟨t1, t2, t3⟩

/-- Chung–Hasan SQR2: three squarings and two multiplications in `Fp2`. -/
def sqr (a : Fp6) : Fp6 :=
  let s0 := a.c0.sqr
  let s1 := (a.c0.mul a.c1).dbl
  let s2 := ((a.c0.sub a.c1).add a.c2).sqr
  let s3 := (a.c1.mul a.c2).dbl
  let s4 := a.c2.sqr
  ⟨s0.add s3.mulXi, s1.add s4.mulXi, ((s1.add s2).add s3).sub s0 |>.sub s4⟩

/-- Multiplication by `v`: `(c0, c1, c2) ↦ (ξ c2, c0, c1)`. -/
@[inline] def mulV (a : Fp6) : Fp6 := ⟨a.c2.mulXi, a.c0, a.c1⟩

/-- Multiplication by an element of `Fp2`. -/
@[inline] def mulFp2 (a : Fp6) (s : Fp2) : Fp6 := ⟨a.c0.mul s, a.c1.mul s, a.c2.mul s⟩

/-- Sparse multiplication by `c1·v` (zkcrypto's `mul_by_1`). -/
def mulBy1 (a : Fp6) (c1 : Fp2) : Fp6 :=
  ⟨(a.c2.mul c1).mulXi, a.c0.mul c1, a.c1.mul c1⟩

/-- Sparse multiplication by `c0 + c1·v` (zkcrypto's `mul_by_01`). -/
def mulBy01 (a : Fp6) (c0 c1 : Fp2) : Fp6 :=
  let aa := a.c0.mul c0
  let bb := a.c1.mul c1
  let t1 := (a.c2.mul c1).mulXi.add aa
  let t2 := ((c0.add c1).mul (a.c0.add a.c1)).sub aa |>.sub bb
  let t3 := (a.c2.mul c0).add bb
  ⟨t1, t2, t3⟩

/-- The inverse through the norm to `Fp2`; `0` maps to `0`. -/
def inv (a : Fp6) : Fp6 :=
  let c0 := a.c0.sqr.sub (a.c1.mul a.c2).mulXi
  let c1 := a.c2.sqr.mulXi.sub (a.c0.mul a.c1)
  let c2 := a.c1.sqr.sub (a.c0.mul a.c2)
  let t := ((a.c2.mul c1).add (a.c1.mul c2)).mulXi.add (a.c0.mul c0)
  let ti := t.inv
  ⟨c0.mul ti, c1.mul ti, c2.mul ti⟩

end Fp6

end LeanLight.Lc.Bls
