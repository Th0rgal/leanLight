import LeanLight.Base.Common

/-!
# Byte helpers the specifications share

The small byte-level vocabulary several specifications use, defined once here: an ASCII
string's bytes, runs of zero bytes, decimal digits, what a collision of Keccak-256 is, and the
ABI's 32-byte words; with Keccak-256 over lists of bytes, `Common.keccak`, in `LeanLight.Base.Common`
so that the light client's runtime code shares it. A module that uses one `export`s it, so
`Spec.Onion.ascii`, `Spec.Tornado.keccak` and `Spec.Multicall.word` all name the definitions
below.
-/

namespace LeanLight.Spec.Common

/-- The bytes of an ASCII string. -/
def ascii (s : String) : List UInt8 := s.toList.map fun c => c.toNat.toUInt8

/-- `n` zero bytes. -/
def zeros (n : Nat) : List UInt8 := List.replicate n 0

/-- An ASCII decimal digit, `0` to `9`. -/
def isDigit (c : UInt8) : Bool := 48 ≤ c.toNat ∧ c.toNat ≤ 57

/-- The pair `p` is a Keccak-256 collision: two different byte strings with one `keccak`.

A binding theorem concludes `IsCollision` of a pair it names explicitly, a function of its own
inputs (`Spec.Tornado.noteCollision`), and never "some collision exists": that is true by
pigeonhole (infinitely many inputs, `2^256` outputs), so a disjunct of that form would make
the theorem prove nothing. With the pair named, the theorem is a reduction: a clash of digests
on different inputs exhibits a collision on those exact bytes. Nothing assumes that collisions
are hard to find. -/
def IsCollision (p : List UInt8 × List UInt8) : Prop := p.1 ≠ p.2 ∧ keccak p.1 = keccak p.2

/-! ## The ABI's words -/

/-- The `w` bytes of `x mod 256 ^ w`, big-endian. -/
def beBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | w + 1, x => (x / 256 ^ w % 256).toUInt8 :: beBytes w x

/-- A number as an ABI word: `v mod 2^256` in 32 bytes, big-endian. -/
def word (v : Nat) : List UInt8 := beBytes 32 v

/-- `n` bytes rounded up to whole 32-byte words. -/
def padded (n : Nat) : Nat := (n + 31) / 32 * 32

/-- An address as an ABI word: twelve zero bytes, then the address. -/
def addressWord (a : List UInt8) : List UInt8 := List.replicate 12 0 ++ a

end LeanLight.Spec.Common
