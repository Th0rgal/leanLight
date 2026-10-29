/-!
# Byte views

The light client reads its input from `ByteArray`s, never from `List UInt8`, which costs about
24 bytes per byte and makes reading at a position linear in it (`docs/spec-16-light-client.md`, "The
Lean package"). Its reads are total: a byte by index, 0 past the end (`byteAt`); and a copy of
a slice (`extract`, `slice`), whose offsets are compared with the buffer's size, and clamped to
it, before `ByteArray.extract` sees them.

The specifications are stated over lists, so each read is proved equal to the same read of
`bs.data.toList`, the bytes as a list: `byteAt_eq`, `extract_eq`, `slice_eq`.
-/

namespace LeanLight.Lc.Bytes

/-- Byte `i` of `bs`, or 0 past its end. -/
def byteAt (bs : ByteArray) (i : Nat) : UInt8 := bs[i]?.getD 0

/-- A copy of the bytes of `bs` from `a` up to `b`, empty unless `a < b`, both offsets clamped
to `bs.size` before the copy. -/
def extract (bs : ByteArray) (a b : Nat) : ByteArray :=
  bs.extract (min a bs.size) (min b bs.size)

/-- `extract`, as a list. -/
def slice (bs : ByteArray) (a b : Nat) : List UInt8 := (extract bs a b).data.toList

theorem size_eq (bs : ByteArray) : bs.data.toList.length = bs.size := by simp

theorem byteAt_eq (bs : ByteArray) (i : Nat) : byteAt bs i = bs.data.toList[i]?.getD 0 := by
  rw [Array.getElem?_toList]
  unfold byteAt
  by_cases h : i < bs.size
  · rw [getElem?_pos bs i h, getElem?_pos bs.data i (by simpa using h)]
    rfl
  · rw [getElem?_neg bs i h, getElem?_neg bs.data i (by simpa using h)]

private theorem take_drop_clamp (l : List UInt8) (a b : Nat) :
    (l.drop (min a l.length)).take (min b l.length - min a l.length) = (l.drop a).take (b - a) := by
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_take, List.getElem?_drop]
  split <;> split
  · rw [Nat.min_eq_left (by omega)]
  · rw [List.getElem?_eq_none (by omega)]
  · rw [List.getElem?_eq_none (by omega)]
  · rfl

/-- What `extract` copies: the bytes from `a` up to `b`, whatever the offsets. -/
theorem extract_eq (bs : ByteArray) (a b : Nat) :
    (extract bs a b).data.toList = (bs.data.toList.take b).drop a := by
  simp only [extract, ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
    List.drop_take]
  simpa using take_drop_clamp bs.data.toList a b

theorem slice_eq (bs : ByteArray) (a b : Nat) : slice bs a b = (bs.data.toList.take b).drop a :=
  extract_eq bs a b

end LeanLight.Lc.Bytes
