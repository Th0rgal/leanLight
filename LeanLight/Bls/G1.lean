import LeanLight.Bls.Fp

/-!
# BLS12-381: G1 on `E: y² = x³ + 4` over `Fp`

Moved from the benchmark's `Bls/Curve.lean` (see `LeanLight.Bls.Fp`). Points are affine (`G1A`, never
the identity) or Jacobian (`G1J`: `(X, Y, Z)` stands for `(X/Z², Y/Z³)`, and `Z = 0` is the
identity). The formulas are the EFD's for `a = 0`: dbl-2009-l, add-2007-bl, madd-2007-bl, the
same as EthLib's `G1.double` and `G1.add` but for the mixed addition.

**Subgroup membership** is `[r]P = O` (`G1A.inSubgroup`), as KeyValidate states it. What runs
is `G1A.inSubgroupFast`: Scott's test (eprint 2021/1130 §6), `σ(P) = [−x²]P` with
`σ(x, y) = (β·x, y)`, about three times faster, for a point with `x ≠ 0`, and `[r]P = O` for any
point that test does not accept. `LeanLightProofs.Bls.Scott` proves Scott's test accepts only
points with `[r]P = O`, so `inSubgroupFast` accepts exactly what `inSubgroup` accepts
(`inSubgroupFast_eq`); every key of G1 passes the fast test, so the slow one runs only on a key
KeyValidate refuses. The cube root of unity `β` is pinned (`beta_eq`) and is the one for which
`σ` acts on G1's generator as `[−x²]` (`beta_acts`), both checked by the kernel.
-/

namespace LeanLight.Lc.Bls

/-- An affine point of `E(Fp)`, never the identity. -/
structure G1A where
  x : Nat
  y : Nat
deriving DecidableEq

/-- A point in Jacobian coordinates; `z = 0` is the identity. -/
structure G1J where
  x : Nat
  y : Nat
  z : Nat

namespace G1J

@[inline] def inf : G1J := ⟨1, 1, 0⟩
@[inline] def ofAffine (p : G1A) : G1J := ⟨p.x, p.y, 1⟩
@[inline] def isInf (p : G1J) : Bool := p.z = 0
@[inline] def neg (p : G1J) : G1J := ⟨p.x, fneg p.y, p.z⟩

/-- Doubling, dbl-2009-l. -/
def dbl (p : G1J) : G1J :=
  if p.z = 0 then p else
  let a := fsqr p.x
  let b := fsqr p.y
  let c := fsqr b
  let d := fdbl (fsub (fsub (fsqr (fadd p.x b)) a) c)
  let e := fadd (fdbl a) a
  let f := fsqr e
  let x3 := fsub f (fdbl d)
  let y3 := fsub (fmul e (fsub d x3)) (fdbl (fdbl (fdbl c)))
  let z3 := fdbl (fmul p.y p.z)
  ⟨x3, y3, z3⟩

/-- Addition, add-2007-bl, with its special cases: either point the identity, `p = q`
(doubling), `p = −q` (the identity). -/
def add (p q : G1J) : G1J :=
  if p.z = 0 then q else if q.z = 0 then p else
  let z1z1 := fsqr p.z
  let z2z2 := fsqr q.z
  let u1 := fmul p.x z2z2
  let u2 := fmul q.x z1z1
  let s1 := fmul (fmul p.y q.z) z2z2
  let s2 := fmul (fmul q.y p.z) z1z1
  if u1 = u2 then (if s1 = s2 then dbl p else inf) else
  let h := fsub u2 u1
  let i := fsqr (fdbl h)
  let j := fmul h i
  let r := fdbl (fsub s2 s1)
  let v := fmul u1 i
  let x3 := fsub (fsub (fsqr r) j) (fdbl v)
  let y3 := fsub (fmul r (fsub v x3)) (fdbl (fmul s1 j))
  let z3 := fmul (fsub (fsub (fsqr (fadd p.z q.z)) z1z1) z2z2) h
  ⟨x3, y3, z3⟩

/-- Mixed addition with an affine point, madd-2007-bl, with the same special cases. -/
def addA (p : G1J) (q : G1A) : G1J :=
  if p.z = 0 then ofAffine q else
  let z1z1 := fsqr p.z
  let u2 := fmul q.x z1z1
  let s2 := fmul (fmul q.y p.z) z1z1
  if p.x = u2 then (if p.y = s2 then dbl p else inf) else
  let h := fsub u2 p.x
  let hh := fsqr h
  let i := fdbl (fdbl hh)
  let j := fmul h i
  let r := fdbl (fsub s2 p.y)
  let v := fmul p.x i
  let x3 := fsub (fsub (fsqr r) j) (fdbl v)
  let y3 := fsub (fmul r (fsub v x3)) (fdbl (fmul p.y j))
  let z3 := fsub (fsub (fsqr (fadd p.z h)) z1z1) hh
  ⟨x3, y3, z3⟩

/-- `[k]p` for an affine `p`: double-and-add from the most significant bit of `k`, with mixed
additions. -/
def mulA (p : G1A) (k : Nat) : G1J := Id.run do
  let mut acc := inf
  let n := Nat.log2 k + 1
  for i in [0:n] do
    acc := dbl acc
    if (k >>> (n - 1 - i)) % 2 = 1 then acc := addA acc p
  return acc

/-- Equality of the points two Jacobian triples stand for. -/
def eq (p q : G1J) : Bool :=
  if p.z = 0 then q.z = 0 else if q.z = 0 then false else
  let z1z1 := fsqr p.z
  let z2z2 := fsqr q.z
  fmul p.x z2z2 = fmul q.x z1z1 &&
    fmul (fmul p.y q.z) z2z2 = fmul (fmul q.y p.z) z1z1

/-- The affine point, by one inversion; `none` for the identity. -/
def toAffine? (p : G1J) : Option G1A :=
  if p.z = 0 then none else
  let zi := finv p.z
  let zi2 := fsqr zi
  some ⟨fmul p.x zi2, fmul p.y (fmul zi2 zi)⟩

end G1J

namespace G1A

@[inline] def neg (p : G1A) : G1A := ⟨p.x, fneg p.y⟩

/-- On `E`: `y² = x³ + 4`. -/
def onCurve (p : G1A) : Bool := fsqr p.y = fadd (fmul (fsqr p.x) p.x) 4

/-- Membership in G1 by `[r]p = O`: the check v1 runs. -/
def inSubgroup (p : G1A) : Bool := (G1J.mulA p R).isInf

end G1A

/-- G1's generator (draft-irtf-cfrg-pairing-friendly-curves, as EthLib's `G1.generator`). -/
def g1Gen : G1A :=
  ⟨0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb,
   0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1⟩

/-! ## Scott's test, for the tests -/

/-- `β`, a primitive cube root of unity in `Fp`: `2^((P−1)/3)` (`beta_eq`), the one for which
`σ` acts on G1 as `[−x²]` (`beta_acts`). -/
def beta : Nat :=
  0x5f19672fdf76ce51ba69c6076a0f77eaddb3a93be6f89688de17d813620a00022e01fffffffefffe

theorem beta_eq : beta = fpow 2 ((P - 1) / 3) := by decide +kernel

/-- The endomorphism `σ(x, y) = (β·x, y)`. -/
@[inline] def G1A.sigma (p : G1A) : G1J := ⟨fmul beta p.x, p.y, 1⟩

theorem beta_acts : (g1Gen.sigma).eq (G1J.mulA g1Gen (X * X)).neg = true := by decide +kernel

/-- Membership in G1 by Scott's test, `σ(p) = [−x²]p`. -/
def G1A.inSubgroupScott (p : G1A) : Bool := p.sigma.eq (G1J.mulA p (X * X)).neg

/-- Membership in G1 as KeyValidate runs it: Scott's test for `x ≠ 0`, else `[r]p = O`. Equal to
`inSubgroup` on the curve (`LeanLightProofs.Bls.Scott.inSubgroupFast_eq`). -/
def G1A.inSubgroupFast (p : G1A) : Bool := (p.x != 0 && p.inSubgroupScott) || p.inSubgroup

end LeanLight.Lc.Bls
