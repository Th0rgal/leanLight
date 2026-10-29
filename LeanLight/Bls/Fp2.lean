import LeanLight.Bls.Fp

/-!
# BLS12-381: `Fp2 = Fp[u]/(u² + 1)`

Moved from the benchmark's `Bls/Field.lean` (see `LeanLight.Bls.Fp`). The tower follows
draft-irtf-cfrg-pairing-friendly-curves and zkcrypto/bls12_381: `Fp2 = Fp[u]/(u² + 1)`,
`Fp6 = Fp2[v]/(v³ − ξ)` with `ξ = 1 + u`, `Fp12 = Fp6[w]/(w² − v)`; EthLib's tower, whose `i` is
`u` here.

Multiplication is Karatsuba with one reduction per coefficient. The square root is the
"complex method" for `P ≡ 3 mod 4`, checked: `sqrt?` returns a root only when it squares to its
argument, so it is sound whatever the arithmetic behind it; that it finds one for every square
is Euler's criterion on the norm, for LC4b. `pow` is square-and-multiply; nothing at run time
calls it, the kernel checks of the pinned constants do (`LeanLight.Bls.Fp12`, `LeanLight.Bls.G2`).
-/

namespace LeanLight.Lc.Bls

/-- `c0 + c1·u`, each coefficient below `P`. -/
structure Fp2 where
  c0 : Nat
  c1 : Nat
deriving DecidableEq

namespace Fp2

@[inline] def zero : Fp2 := ⟨0, 0⟩
@[inline] def one : Fp2 := ⟨1, 0⟩
@[inline] def add (a b : Fp2) : Fp2 := ⟨fadd a.c0 b.c0, fadd a.c1 b.c1⟩
@[inline] def sub (a b : Fp2) : Fp2 := ⟨fsub a.c0 b.c0, fsub a.c1 b.c1⟩
@[inline] def neg (a : Fp2) : Fp2 := ⟨fneg a.c0, fneg a.c1⟩
@[inline] def dbl (a : Fp2) : Fp2 := ⟨fdbl a.c0, fdbl a.c1⟩
/-- The conjugate `c0 − c1·u`, which is the Frobenius `a ↦ a^P`. -/
@[inline] def conj (a : Fp2) : Fp2 := ⟨a.c0, fneg a.c1⟩
@[inline] def isZero (a : Fp2) : Bool := a.c0 = 0 && a.c1 = 0
@[inline] def eq (a b : Fp2) : Bool := a.c0 = b.c0 && a.c1 = b.c1

/-- Karatsuba with one reduction per coefficient: `(a0 b0 − a1 b1) + (a0 b1 + a1 b0)·u`. -/
@[inline] def mul (a b : Fp2) : Fp2 :=
  let t0 := a.c0 * b.c0
  let t1 := a.c1 * b.c1
  let t2 := (a.c0 + a.c1) * (b.c0 + b.c1)
  ⟨(t0 + PP - t1) % P, (t2 - t0 - t1) % P⟩

/-- `(a0 + a1 u)² = (a0 + a1)(a0 − a1) + 2 a0 a1 u`. -/
@[inline] def sqr (a : Fp2) : Fp2 :=
  ⟨(a.c0 + a.c1) * (a.c0 + P - a.c1) % P, 2 * a.c0 * a.c1 % P⟩

/-- Multiplication by an element of `Fp`. -/
@[inline] def mulFp (a : Fp2) (s : Nat) : Fp2 := ⟨a.c0 * s % P, a.c1 * s % P⟩

/-- Multiplication by `ξ = 1 + u`. -/
@[inline] def mulXi (a : Fp2) : Fp2 := ⟨fsub a.c0 a.c1, fadd a.c0 a.c1⟩

/-- The inverse, `conj a / (a0² + a1²)`; `0` maps to `0`. -/
def inv (a : Fp2) : Fp2 :=
  let t := finv ((a.c0 * a.c0 + a.c1 * a.c1) % P)
  ⟨a.c0 * t % P, fneg (a.c1 * t % P)⟩

/-- `a^e` by square-and-multiply over the bits of `e`, most significant first. -/
def pow (a : Fp2) (e : Nat) : Fp2 := Id.run do
  let mut acc := one
  let n := Nat.log2 e + 1
  for k in [0:n] do
    acc := sqr acc
    if (e >>> (n - 1 - k)) % 2 = 1 then acc := mul acc a
  return acc

/-- A square root for `P ≡ 3 mod 4` (the "complex method"): with `n = a0² + a1²` and `γ = √n`
in `Fp`, `x0 = √((a0 ± γ)/2)` and `x1 = a1 / (2 x0)`. Kept only when it squares to `a`;
`none` when `a` is not a square. -/
def sqrt? (a : Fp2) : Option Fp2 :=
  if a.c1 = 0 then
    match fsqrt? a.c0 with
    | some y => some ⟨y, 0⟩
    | none =>
      -- a0 is not a square in Fp: √a0 = √(−a0)·u, as u² = −1.
      match fsqrt? (fneg a.c0) with
      | some y => some ⟨0, y⟩
      | none => none
  else
    match fsqrt? ((a.c0 * a.c0 + a.c1 * a.c1) % P) with
    | none => none
    | some g =>
      let half := (P + 1) / 2
      let x0? := match fsqrt? (fadd a.c0 g * half % P) with
        | some x0 => some x0
        | none => fsqrt? (fsub a.c0 g * half % P)
      match x0? with
      | none => none
      | some x0 =>
        let y : Fp2 := ⟨x0, a.c1 * finv (fdbl x0) % P⟩
        if (sqr y).eq a then some y else none

/-- Euler's criterion in `Fp2`: `a` is a square exactly when its norm `a0² + a1²` is a square
in `Fp`. -/
@[inline] def isSquare (a : Fp2) : Bool := fIsSquare ((a.c0 * a.c0 + a.c1 * a.c1) % P)

/-- RFC 9380 §4.1's `sgn0` for `m = 2`. -/
@[inline] def sgn0 (a : Fp2) : Bool :=
  a.c0 % 2 = 1 || (a.c0 = 0 && a.c1 % 2 = 1)

/-- ZCash's "lexicographically largest" for `Fp2`: `c1`'s, or `c0`'s when `c1` is zero. -/
@[inline] def large (a : Fp2) : Bool := if a.c1 = 0 then fLarge a.c0 else fLarge a.c1

end Fp2

/-- `ξ = 1 + u`, the cubic non-residue of the tower. -/
def xi : Fp2 := ⟨1, 1⟩

end LeanLight.Lc.Bls
