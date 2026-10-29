import LeanLight.Bytes

/-!
# SSZ: reading fields

What the typed decoders (`LeanLight.Ssz.Containers`) read from a `ByteArray`: little-endian
unsigned integers (`readLE`, the same digits as ssz-specs' `readUint`), the bytes of a field
(`slice`, a copy clamped to the buffer, `LeanLight.Bytes.extract`) and runs of 32-byte roots
(`roots`). Every read is total: a byte past the end reads 0 and a slice past the end is short,
and the decoders compare every offset and size with the buffer's before they read, so neither
happens on an input they accept.

Recursion here is over a field's width, at most 32 bytes, fixed by the type, never by the
input; counts of roots are fixed by the type too (at most 512).
-/

namespace LeanLight.Lc.Ssz

open LeanLight.Lc.Bytes (byteAt extract)

/-- The unsigned integer in the `w` bytes of `bs` from `off`, little-endian, a byte past the
end reading 0: ssz-specs' `readUint` over a `ByteArray`. -/
def readLE (bs : ByteArray) (off : Nat) : Nat → Nat
  | 0 => 0
  | w + 1 => (byteAt bs off).toNat + 256 * readLE bs (off + 1) w

/-- A `uint64` field at `off`. -/
def u64 (bs : ByteArray) (off : Nat) : Nat := readLE bs off 8

/-- A 4-byte offset at `off`. -/
def offsetAt (bs : ByteArray) (off : Nat) : Nat := readLE bs off 4

/-- The `n` bytes of `bs` from `off`, a copy clamped to the buffer. -/
def slice (bs : ByteArray) (off n : Nat) : ByteArray := extract bs off (off + n)

/-- `k` consecutive fields of `w` bytes from `off` (a `Vector[ByteVector[w], k]`). -/
def fields (bs : ByteArray) (off w k : Nat) : Array ByteArray :=
  Array.ofFn (n := k) fun i => slice bs (off + w * i.val) w

/-- `k` consecutive 32-byte roots from `off` (a Merkle branch, `Vector[Bytes32, k]`). -/
def roots (bs : ByteArray) (off k : Nat) : Array ByteArray := fields bs off 32 k

end LeanLight.Lc.Ssz
