import LeanLight.Bls.Fp6

/-!
# BLS12-381: `Fp12 = Fp6[w]/(w² − v)`, and the Frobenius

Moved from the benchmark's `Bls/Field.lean` (see `LeanLight.Bls.Fp`). `mulBy014` is zkcrypto's
sparse product by a Miller-loop line.

**The Frobenius** `a ↦ a^P` acts on `Fp6` and `Fp12` through three constants of `Fp2`,
`ξ^((P−1)/3)`, `ξ^(2(P−1)/3)` and `ξ^((P−1)/6)`. The benchmark computed them when the program
started; here they are literals, each checked by the kernel against its definition
(`frobV1_eq`, `frobV2_eq`, `frobW_eq`).
-/

namespace LeanLight.Lc.Bls

/-- `c0 + c1·w`. -/
structure Fp12 where
  c0 : Fp6
  c1 : Fp6
deriving DecidableEq

namespace Fp12

@[inline] def one : Fp12 := ⟨Fp6.one, Fp6.zero⟩
@[inline] def eq (a b : Fp12) : Bool := a.c0.eq b.c0 && a.c1.eq b.c1
@[inline] def isOne (a : Fp12) : Bool := a.eq one
/-- The conjugate `c0 − c1·w`, which is `a^(P⁶)`, and the inverse in the cyclotomic subgroup. -/
@[inline] def conj (a : Fp12) : Fp12 := ⟨a.c0, a.c1.neg⟩

def mul (a b : Fp12) : Fp12 :=
  let aa := a.c0.mul b.c0
  let bb := a.c1.mul b.c1
  let c1 := ((a.c0.add a.c1).mul (b.c0.add b.c1)).sub aa |>.sub bb
  ⟨aa.add bb.mulV, c1⟩

/-- Complex squaring: two `Fp6` multiplications. -/
def sqr (a : Fp12) : Fp12 :=
  let ab := a.c0.mul a.c1
  let c0 := ((a.c0.add a.c1).mul (a.c0.add a.c1.mulV)).sub ab |>.sub ab.mulV
  ⟨c0, ab.dbl⟩

/-- The inverse through the norm to `Fp6`; `0` maps to `0`. -/
def inv (a : Fp12) : Fp12 :=
  let t := (a.c0.sqr.sub a.c1.sqr.mulV).inv
  ⟨a.c0.mul t, (a.c1.mul t).neg⟩

/-- Sparse multiplication by `c0 + c1·v + c4·v·w` (zkcrypto's `mul_by_014`). -/
def mulBy014 (a : Fp12) (c0 c1 c4 : Fp2) : Fp12 :=
  let aa := a.c0.mulBy01 c0 c1
  let bb := a.c1.mulBy1 c4
  let o := c1.add c4
  let c1' := ((a.c1.add a.c0).mulBy01 c0 o).sub aa |>.sub bb
  ⟨bb.mulV.add aa, c1'⟩

end Fp12

/-! ## The Frobenius -/

/-- `ξ^((P−1)/3)` (`frobV1_eq`). -/
def frobV1 : Fp2 :=
  ⟨0, 0x1a0111ea397fe699ec02408663d4de85aa0d857d89759ad4897d29650fb85f9b409427eb4f49fffd8bfd00000000aaac⟩

/-- `ξ^(2(P−1)/3)` (`frobV2_eq`). -/
def frobV2 : Fp2 :=
  ⟨0x1a0111ea397fe699ec02408663d4de85aa0d857d89759ad4897d29650fb85f9b409427eb4f49fffd8bfd00000000aaad, 0⟩

/-- `ξ^((P−1)/6)` (`frobW_eq`). -/
def frobW : Fp2 :=
  ⟨0x1904d3bf02bb0667c231beb4202c0d1f0fd603fd3cbd5f4f7b2443d784bab9c4f67ea53d63e7813d8d0775ed92235fb8,
   0xfc3e2b36c4e03288e9e902231f9fb854a14787b6c7b36fec0c8ec971f63c5f282d5ac14d6c7ec22cf78a126ddc4af3⟩

theorem frobV1_eq : frobV1 = Fp2.pow xi ((P - 1) / 3) := by decide +kernel
theorem frobV2_eq : frobV2 = Fp2.pow xi (2 * (P - 1) / 3) := by decide +kernel
theorem frobW_eq : frobW = Fp2.pow xi ((P - 1) / 6) := by decide +kernel

/-- The Frobenius on `Fp6`: `v^P = ξ^((P−1)/3)·v`. -/
@[inline] def Fp6.frob (a : Fp6) : Fp6 :=
  ⟨a.c0.conj, a.c1.conj.mul frobV1, a.c2.conj.mul frobV2⟩

/-- The Frobenius on `Fp12`: `w^P = ξ^((P−1)/6)·w`. -/
@[inline] def Fp12.frob (a : Fp12) : Fp12 :=
  ⟨a.c0.frob, a.c1.frob.mulFp2 frobW⟩

end LeanLight.Lc.Bls
