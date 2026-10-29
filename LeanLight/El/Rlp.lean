import LeanLight.Base.Rlp
import LeanLight.Bytes

/-!
# RLP decoding, one item at a time

The inverse of `Spec.Rlp`'s encoding (Yellow Paper, Appendix B), accepting only canonical
input: the encoding `Spec.Rlp` writes, and nothing else. This is the part of the decoder that
runs, in the light client (leanKohakuDesktop's `spec/16-light-client.md`, "The Lean package"); the whole-structure
decoder `decodeTree`, a specification that is never run, stays in `LeanLightProofs.Spec.RlpDecode`.

**One item.** `decodeHead` reads the first bytes of an item, as a decoder does: a list or a
byte array, how many bytes come before the payload, and the payload's length. It refuses a
single byte below `0x80` written with a prefix, a length below 56 written in the long form, a
length with a leading zero byte, and a payload that runs past the end. Its two theorems are
the round trip, each way:

- `decodeHead_encodeItem`: on an encoding followed by anything, `decodeHead` finds the
  encoding's payload and its end (decode ∘ encode is the identity);
- `encodeItem_decodeHead`: whatever `decodeHead` accepts is followed by its payload, and the
  bytes it spans are exactly the encoding of that payload (encode ∘ decode is the identity on
  accepted input, which is what canonical means).

**Positions.** The code that runs, `lkd_verified::rlp_decode`, reads one level per call with no
recursion, and is `itemAt` and `itemsAt` here: an item at a position of a buffer, and the items
of a list payload. `itemAt_span` says what an item found is (`Span.Found`): the canonical
encoding of its payload, within the bytes read; `itemsAt_spans` adds that the items of a list
payload come one after the other, spanning the payload exactly.
-/

namespace LeanLight.Spec.RlpDecode

open LeanLight.Spec.Rlp

/-- What the first bytes of an item say: a list or a byte array, the number of bytes before the
payload, and the payload's length. -/
structure Head where
  list : Bool
  offset : Nat
  length : Nat
deriving DecidableEq, Repr

/-- The number of bytes the item takes. -/
def Head.size (h : Head) : Nat := h.offset + h.length

/-- An item whose first byte gives its payload's length, `len < 56`: refused when the payload
runs past the end, or when it is a single byte below `0x80` in a byte array. -/
def short (list : Bool) (len : Nat) (rest : Bytes) : Option Head :=
  if len ≤ rest.length ∧ ¬(list = false ∧ len = 1 ∧ (rest[0]?.getD 0).toNat < 128) then
    some ⟨list, 1, len⟩
  else none

/-- An item whose first byte says its payload's length takes the next `n` bytes: refused when
that length has a leading zero byte, is below 56, or runs past the end. -/
def long (list : Bool) (n : Nat) (rest : Bytes) : Option Head :=
  if n ≤ rest.length ∧ rest[0]?.getD 0 ≠ 0 ∧ 56 ≤ beValue (rest.take n) ∧
      beValue (rest.take n) ≤ rest.length - n then
    some ⟨list, 1 + n, beValue (rest.take n)⟩
  else none

/-- The head of the item at the front of `w`, or `none` unless `w` starts with a canonical
item. -/
def decodeHead : Bytes → Option Head
  | [] => none
  | b :: rest =>
    if b.toNat < 128 then some ⟨false, 0, 1⟩
    else if b.toNat < 184 then short false (b.toNat - 128) rest
    else if b.toNat < 192 then long false (b.toNat - 183) rest
    else if b.toNat < 248 then short true (b.toNat - 192) rest
    else long true (b.toNat - 247) rest

/-- The payload of the item at the front of `w`, whose head is `h`. -/
def payload (w : Bytes) (h : Head) : Bytes := (w.drop h.offset).take h.length

/-- R_l or R_b: the encoding of a list payload or a byte array. -/
def encodeItem (list : Bool) (p : Bytes) : Option Bytes :=
  if list then encodeList p else encodeBytes p

/-! ## Big-endian lengths -/

private theorem toUInt8_toNat {n : Nat} (h : n < 256) : n.toUInt8.toNat = n := by
  simp [Nat.toUInt8, Nat.mod_eq_of_lt h]

/-- The minimal big-endian bytes of a nonzero number start with a nonzero byte. -/
theorem be_head_ne_zero : ∀ {x : Nat}, x ≠ 0 → (be x)[0]?.getD 0 ≠ 0 := by
  intro x
  induction x using Nat.strongRecOn with
  | ind x ih =>
    intro hx
    rw [be_pos hx]
    by_cases hq : x / 256 = 0
    · rw [hq, be_zero]
      simp only [List.nil_append, List.getElem?_cons_zero, Option.getD_some]
      intro h0
      have := congrArg UInt8.toNat h0
      rw [toUInt8_toNat (Nat.mod_lt _ (by omega))] at this
      simp at this
      omega
    · have hne := be_ne_nil hq
      have := ih (x / 256) (by omega) hq
      cases hb : be (x / 256) with
      | nil => exact absurd hb hne
      | cons c cs => rw [hb] at this; simpa using this

theorem be_length_pos {x : Nat} (h : x ≠ 0) : 0 < (be x).length := by
  have := be_ne_nil h
  cases hb : be x with
  | nil => exact absurd hb this
  | cons => simp

/-! ## The encodings, case by case -/

theorem encodeBytes_eq {x e : Bytes} (h : encodeBytes x = some e) :
    (x.length = 1 ∧ (x[0]?.getD 0).toNat < 128 ∧ e = x) ∨
    (¬(x.length = 1 ∧ (x[0]?.getD 0).toNat < 128) ∧ x.length < 56 ∧
      e = (128 + x.length).toUInt8 :: x) ∨
    (56 ≤ x.length ∧ x.length < 2 ^ 64 ∧
      e = (183 + (be x.length).length).toUInt8 :: (be x.length ++ x)) := by
  unfold encodeBytes at h
  split at h
  · rename_i hc
    left; cases h
    exact ⟨hc.1, by simpa [UInt8.lt_iff_toNat_lt] using hc.2, rfl⟩
  · rename_i hc
    split at h
    · rename_i hl
      right; left; cases h
      exact ⟨by simpa [UInt8.lt_iff_toNat_lt] using hc, hl, rfl⟩
    · rename_i hl
      split at h
      · rename_i hl'; right; right; cases h; exact ⟨by omega, hl', rfl⟩
      · contradiction

theorem encodeList_eq {s e : Bytes} (h : encodeList s = some e) :
    (s.length < 56 ∧ e = (192 + s.length).toUInt8 :: s) ∨
    (56 ≤ s.length ∧ s.length < 2 ^ 64 ∧
      e = (247 + (be s.length).length).toUInt8 :: (be s.length ++ s)) := by
  unfold encodeList at h
  split at h
  · rename_i hl; left; cases h; exact ⟨hl, rfl⟩
  · rename_i hl
    split at h
    · rename_i hl'; right; cases h; exact ⟨by omega, hl', rfl⟩
    · contradiction

/-- An encoding ends with its payload. -/
theorem encodeItem_suffix {l : Bool} {p e : Bytes} (h : encodeItem l p = some e) :
    p.length ≤ e.length ∧ e.drop (e.length - p.length) = p := by
  cases l with
  | false =>
    rcases encodeBytes_eq h with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
    · simp
    · simp
    · simp only [List.length_cons, List.length_append]
      refine ⟨by omega, ?_⟩
      rw [show (be p.length).length + p.length + 1 - p.length = 1 + (be p.length).length by omega,
        ← List.drop_drop, List.drop_one, List.tail_cons, List.drop_left' rfl]
  | true =>
    rcases encodeList_eq h with ⟨-, rfl⟩ | ⟨-, -, rfl⟩
    · simp
    · simp only [List.length_cons, List.length_append]
      refine ⟨by omega, ?_⟩
      rw [show (be p.length).length + p.length + 1 - p.length = 1 + (be p.length).length by omega,
        ← List.drop_drop, List.drop_one, List.tail_cons, List.drop_left' rfl]

/-- A list's encoding has at least one byte before its payload. -/
theorem encodeList_length {p e : Bytes} (h : encodeList p = some e) : p.length < e.length := by
  rcases encodeList_eq h with ⟨-, rfl⟩ | ⟨-, -, rfl⟩
  · simp
  · simp; omega

/-! ## Decode ∘ encode -/

/-- `decodeHead` reads an encoding, followed by anything, back: its payload is the encoded
bytes and it ends where the encoding does. -/
theorem decodeHead_encodeItem {l : Bool} {p e : Bytes} (h : encodeItem l p = some e)
    (r : Bytes) : decodeHead (e ++ r) = some ⟨l, e.length - p.length, p.length⟩ := by
  cases l with
  | false =>
    rcases encodeBytes_eq h with ⟨h1, h2, he⟩ | ⟨hc, h2, rfl⟩ | ⟨h1, h2, rfl⟩
    · rw [he]
      match p, h1 with
      | [b], _ =>
        simp only [List.getElem?_cons_zero, Option.getD_some] at h2
        simp [decodeHead, h2]
    · have hb := toUInt8_toNat (n := 128 + p.length) (by omega)
      simp only [decodeHead, List.cons_append, hb]
      rw [if_neg (by omega), if_pos (by omega)]
      unfold short
      rw [if_pos]
      · simp
      · refine ⟨by simp, ?_⟩
        rintro ⟨-, h1, h3⟩
        apply hc
        have hp1 : p.length = 1 := by omega
        refine ⟨hp1, ?_⟩
        obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hp1
        simpa using h3
    · have h8 := be_length_le_eight h2
      have hpos := be_length_pos (x := p.length) (by omega)
      have hb := toUInt8_toNat (n := 183 + (be p.length).length) (by omega)
      simp only [decodeHead, List.cons_append, hb]
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      unfold long
      rw [show 183 + (be p.length).length - 183 = (be p.length).length by omega,
        List.append_assoc, List.take_left' rfl, beValue_be, if_pos]
      · simp; omega
      · refine ⟨by simp, ?_, h1, by simp⟩
        have := be_head_ne_zero (x := p.length) (by omega)
        cases hbe : be p.length with
        | nil => exact absurd hbe (be_ne_nil (by omega))
        | cons c cs => rw [hbe] at this; simpa using this
  | true =>
    rcases encodeList_eq h with ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩
    · have hb := toUInt8_toNat (n := 192 + p.length) (by omega)
      simp only [decodeHead, List.cons_append, hb]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      unfold short
      rw [if_pos]
      · simp
      · exact ⟨by simp, by simp⟩
    · have h8 := be_length_le_eight h2
      have hpos := be_length_pos (x := p.length) (by omega)
      have hb := toUInt8_toNat (n := 247 + (be p.length).length) (by omega)
      simp only [decodeHead, List.cons_append, hb]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      unfold long
      rw [show 247 + (be p.length).length - 247 = (be p.length).length by omega,
        List.append_assoc, List.take_left' rfl, beValue_be, if_pos]
      · simp; omega
      · refine ⟨by simp, ?_, h1, by simp⟩
        have := be_head_ne_zero (x := p.length) (by omega)
        cases hbe : be p.length with
        | nil => exact absurd hbe (be_ne_nil (by omega))
        | cons c cs => rw [hbe] at this; simpa using this

/-! ## Encode ∘ decode -/

/-- What `decodeHead` accepts fits in the bytes it read, is at least one byte long, and a
list has at least one byte before its payload. -/
theorem decodeHead_size {w : Bytes} {h : Head} (hd : decodeHead w = some h) :
    h.size ≤ w.length ∧ 0 < h.size ∧ (h.list → 0 < h.offset) := by
  match w, hd with
  | b :: rest, hd =>
    simp only [decodeHead] at hd
    split at hd
    · cases hd; simp [Head.size]
    split at hd
    · unfold short at hd; split at hd
      · rename_i hc; cases hd; simp [Head.size]; omega
      · contradiction
    split at hd
    · unfold long at hd; split at hd
      · rename_i hc; cases hd; simp [Head.size]; omega
      · contradiction
    split at hd
    · unfold short at hd; split at hd
      · rename_i hc; cases hd; simp [Head.size]; omega
      · contradiction
    · unfold long at hd; split at hd
      · rename_i hc; cases hd; simp [Head.size]; omega
      · contradiction

theorem payload_length {w : Bytes} {h : Head} (hd : decodeHead w = some h) :
    (payload w h).length = h.length := by
  have := (decodeHead_size hd).1
  simp [payload, Head.size] at *
  omega

private theorem take_long (b : UInt8) (rest : Bytes) (n L : Nat) (hn : n ≤ rest.length)
    (hL : L ≤ rest.length - n) :
    (b :: rest).take (1 + n + L) = b :: (rest.take n ++ (rest.drop n).take L) := by
  rw [show 1 + n + L = (n + L) + 1 by omega, List.take_succ_cons]
  congr 1
  conv => lhs; rw [← List.take_append_drop n rest]
  rw [List.take_append, List.take_of_length_le (by simp; omega)]
  simp; omega

theorem encodeBytes_short {x : Bytes} (hc : ¬(x.length = 1 ∧ (x[0]?.getD 0).toNat < 128))
    (h : x.length < 56) : encodeBytes x = some ((128 + x.length).toUInt8 :: x) := by
  unfold encodeBytes
  rw [if_neg (by simpa [UInt8.lt_iff_toNat_lt] using hc), if_pos h]

theorem encodeBytes_long {x : Bytes} (h : 56 ≤ x.length) (h' : x.length < 2 ^ 64) :
    encodeBytes x = some ((183 + (be x.length).length).toUInt8 :: (be x.length ++ x)) := by
  unfold encodeBytes
  rw [if_neg (by omega), if_neg (by omega), if_pos h']

theorem encodeList_short {s : Bytes} (h : s.length < 56) :
    encodeList s = some ((192 + s.length).toUInt8 :: s) := by
  unfold encodeList
  rw [if_pos h]

theorem encodeList_long {s : Bytes} (h : 56 ≤ s.length) (h' : s.length < 2 ^ 64) :
    encodeList s = some ((247 + (be s.length).length).toUInt8 :: (be s.length ++ s)) := by
  unfold encodeList
  rw [if_neg (by omega), if_pos h']

/-- What the long form's conditions give: the length bytes are the minimal big-endian bytes
of the length, which is below 2^64, and the payload is there in full. -/
private theorem long_parts {n : Nat} {rest : Bytes} (hn8 : n ≤ 8) (hpos : 0 < n)
    (hn : n ≤ rest.length) (h0 : rest[0]?.getD 0 ≠ 0)
    (hL : beValue (rest.take n) ≤ rest.length - n) :
    be (beValue (rest.take n)) = rest.take n ∧ beValue (rest.take n) < 2 ^ 64 ∧
      ((rest.drop n).take (beValue (rest.take n))).length = beValue (rest.take n) := by
  refine ⟨?_, ?_, by simp; omega⟩
  · apply be_beValue _ _ rfl
    intro c hc
    cases rest with
    | nil => simp at hn; omega
    | cons d ds =>
      have : (List.take n (d :: ds)).head? = some d := by
        rw [show n = (n - 1) + 1 by omega, List.take_succ_cons]
        rfl
      rw [this] at hc
      cases hc
      simpa using h0
  · have := beValue_lt (rest.take n)
    have hlen : (rest.take n).length ≤ 8 := by simp; omega
    have : 256 ^ (rest.take n).length ≤ 256 ^ 8 := Nat.pow_le_pow_right (by omega) hlen
    omega

private theorem first_byte {b : UInt8} {base n : Nat} (hn : n = b.toNat - base) (hb : base ≤ b.toNat)
    (h : base + n < 256) : (base + n).toUInt8 = b := by
  apply UInt8.toNat_inj.mp
  rw [toUInt8_toNat h]
  omega

/-- Whatever `decodeHead` accepts spans exactly the canonical encoding of its payload. -/
theorem encodeItem_decodeHead {w : Bytes} {h : Head} (hd : decodeHead w = some h) :
    encodeItem h.list (payload w h) = some (w.take h.size) := by
  match w, hd with
  | b :: rest, hd =>
    have hbl := b.toNat_lt
    simp only [decodeHead] at hd
    split at hd
    · rename_i hb
      cases hd
      show encodeBytes (((b :: rest).drop 0).take 1) = some ((b :: rest).take (0 + 1))
      simp only [List.drop_zero, Nat.zero_add, List.take_succ_cons, List.take_zero]
      unfold encodeBytes
      rw [if_pos ⟨rfl, by simp [UInt8.lt_iff_toNat_lt]; omega⟩]
    split at hd
    · rename_i h1 h2
      unfold short at hd
      split at hd
      · rename_i hc
        cases hd
        have hlen : (rest.take (b.toNat - 128)).length = b.toNat - 128 := by simp; omega
        unfold encodeItem payload Head.size
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [List.drop_one, List.tail_cons, encodeBytes_short _ (by omega), hlen,
          show 1 + (b.toNat - 128) = (b.toNat - 128) + 1 by omega, List.take_succ_cons,
          first_byte rfl (by omega) (by omega)]
        rintro ⟨h3, h4⟩
        apply hc.2
        refine ⟨rfl, by omega, ?_⟩
        cases rest with
        | nil => simp at h3
        | cons c cs =>
          rw [show b.toNat - 128 = 0 + 1 by omega, List.take_succ_cons] at h4
          simpa using h4
      · contradiction
    split at hd
    · rename_i h1 h2 h3
      unfold long at hd
      split at hd
      · rename_i hc
        obtain ⟨hn, h0, h56, hL⟩ := hc
        cases hd
        obtain ⟨hbe, hlt, hplen⟩ := long_parts (by omega) (by omega) hn h0 hL
        unfold encodeItem payload Head.size
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [Nat.add_comm 1, List.drop_succ_cons, encodeBytes_long (by rw [hplen]; omega)
          (by rw [hplen]; exact hlt), hplen, hbe, Nat.add_comm (b.toNat - 183) 1,
          take_long b rest _ _ hn hL]
        have hk : (rest.take (b.toNat - 183)).length = b.toNat - 183 := by simp; omega
        rw [hk, first_byte rfl (by omega) (by omega)]
      · contradiction
    split at hd
    · rename_i h1 h2 h3 h4
      unfold short at hd
      split at hd
      · rename_i hc
        cases hd
        have hlen : (rest.take (b.toNat - 192)).length = b.toNat - 192 := by simp; omega
        unfold encodeItem payload Head.size
        simp only [↓reduceIte]
        rw [List.drop_one, List.tail_cons, encodeList_short (by omega), hlen,
          show 1 + (b.toNat - 192) = (b.toNat - 192) + 1 by omega, List.take_succ_cons,
          first_byte rfl (by omega) (by omega)]
      · contradiction
    · rename_i h1 h2 h3 h4
      unfold long at hd
      split at hd
      · rename_i hc
        obtain ⟨hn, h0, h56, hL⟩ := hc
        cases hd
        obtain ⟨hbe, hlt, hplen⟩ := long_parts (by omega) (by omega) hn h0 hL
        unfold encodeItem payload Head.size
        simp only [↓reduceIte]
        rw [Nat.add_comm 1, List.drop_succ_cons, encodeList_long (by rw [hplen]; omega)
          (by rw [hplen]; exact hlt), hplen, hbe, Nat.add_comm (b.toNat - 247) 1,
          take_long b rest _ _ hn hL]
        have hk : (rest.take (b.toNat - 247)).length = b.toNat - 247 := by simp; omega
        rw [hk, first_byte rfl (by omega) (by omega)]
      · contradiction

/-- A canonical item is determined by the bytes it spans: two heads read from bytes that agree
on the first one's span are equal. -/
theorem decodeHead_take {w : Bytes} {h : Head} (hd : decodeHead w = some h) (r : Bytes) :
    decodeHead (w.take h.size ++ r) = some h := by
  have he := encodeItem_decodeHead hd
  have := decodeHead_encodeItem he r
  rw [this, payload_length hd]
  have hs := (decodeHead_size hd).1
  rw [List.length_take, Nat.min_eq_left hs]
  cases h
  simp [Head.size]

/-! ## Positions in a buffer: what the code computes -/

/-- An item found in a buffer: a list or a byte array, the position of its first byte, and
where its payload starts and, with the item, ends. -/
structure Span where
  list : Bool
  pos : Nat
  start : Nat
  stop : Nat
deriving DecidableEq, Repr, Inhabited

/-- The bytes of `bs` from `pos` up to `stop`. -/
def window (bs : Bytes) (pos stop : Nat) : Bytes := (bs.take stop).drop pos

/-- The item at `pos` of `bs`, read no further than `stop`: `lkd_verified::rlp_decode::item`. -/
def itemAt (bs : Bytes) (pos stop : Nat) : Option Span :=
  if stop ≤ bs.length ∧ pos < stop then
    (decodeHead (window bs pos stop)).map fun h => ⟨h.list, pos, pos + h.offset, pos + h.size⟩
  else none

/-- The items from `p` up to `stop`, one after the other. `n` is fuel. -/
def itemsF : Nat → Bytes → Nat → Nat → Option (List Span)
  | 0, _, _, _ => none
  | n + 1, bs, p, stop =>
    if p < stop then
      match itemAt bs p stop with
      | none => none
      | some it => (itemsF n bs it.stop stop).map (it :: ·)
    else some []

/-- `itemsF` with the items gathered newest first in `acc` and reversed at the end, so that
it runs in constant stack however many items a hostile list holds (AGENTS.md, Runtime Lean):
`itemsF_eq_acc` makes the compiled code run it (`itemsAcc`) in place of `itemsF`. -/
def itemsAccF : Nat → Bytes → Nat → Nat → List Span → Option (List Span)
  | 0, _, _, _, _ => none
  | n + 1, bs, p, stop, acc =>
    if p < stop then
      match itemAt bs p stop with
      | none => none
      | some it => itemsAccF n bs it.stop stop (it :: acc)
    else some acc.reverse

theorem itemsAccF_eq : ∀ (n : Nat) (bs : Bytes) (p stop : Nat) (acc : List Span),
    itemsAccF n bs p stop acc = (itemsF n bs p stop).map (acc.reverse ++ ·)
  | 0, _, _, _, _ => rfl
  | n + 1, bs, p, stop, acc => by
    simp only [itemsAccF, itemsF]
    split
    · cases itemAt bs p stop with
      | none => rfl
      | some it =>
        simp only [itemsAccF_eq n bs it.stop stop (it :: acc), Option.map_map]
        congr 1; funext l; simp
    · simp

/-- `itemsAccF` from an empty accumulator. -/
def itemsAcc (n : Nat) (bs : Bytes) (p stop : Nat) : Option (List Span) := itemsAccF n bs p stop []

@[csimp] theorem itemsF_eq_acc : @itemsF = @itemsAcc := by
  funext n bs p stop
  simp [itemsAcc, itemsAccF_eq]

/-- The items of the list payload from `start` up to `stop`:
`lkd_verified::rlp_decode::items`. -/
def itemsAt (bs : Bytes) (start stop : Nat) : Option (List Span) :=
  if start ≤ stop ∧ stop ≤ bs.length then itemsF (stop - start + 1) bs start stop else none

/-- What an item found at `pos` of `bs`, read no further than `stop`, is: it starts at `pos`; its
payload `[start, stop)` follows its prefix; it takes at least one byte and ends by `stop`, which
is within the buffer; a list has a prefix; and its bytes are the canonical encoding (R_b or R_l)
of its payload. -/
def Span.Found (bs : Bytes) (pos stop : Nat) (it : Span) : Prop :=
  it.pos = pos ∧ pos ≤ it.start ∧ it.start ≤ it.stop ∧ pos < it.stop ∧ it.stop ≤ stop ∧
    stop ≤ bs.length ∧ (it.list → pos < it.start) ∧
    encodeItem it.list (window bs it.start it.stop) = some (window bs pos it.stop)

theorem window_length {bs : Bytes} {pos stop : Nat} (h : stop ≤ bs.length) :
    (window bs pos stop).length = stop - pos := by
  simp [window]; omega

theorem window_window (bs : Bytes) {p e a b : Nat} (h : p + b ≤ e) :
    window (window bs p e) a b = window bs (p + a) (p + b) := by
  simp only [window]
  rw [List.take_drop, List.take_take, Nat.min_eq_left h, List.drop_drop]

theorem window_append (bs : Bytes) {p m e : Nat} (h1 : p ≤ m) (h2 : m ≤ e) :
    window bs p m ++ window bs m e = window bs p e := by
  simp only [window]
  conv => rhs; rw [← List.take_append_drop (m - p) ((bs.take e).drop p)]
  rw [List.take_drop, List.take_take, Nat.min_eq_left (by omega), List.drop_drop,
    Nat.add_sub_of_le h1]

theorem payload_eq_window (w : Bytes) (h : Head) : payload w h = window w h.offset h.size := by
  simp only [payload, window, Head.size]
  rw [List.take_drop]

theorem take_eq_window (w : Bytes) (n : Nat) : w.take n = window w 0 n := by
  simp [window]

/-- What an item found at a position is: the canonical encoding of its payload, within
`[pos, stop)`, at least one byte long (`Span.Found`). -/
theorem itemAt_span {bs : Bytes} {pos stop : Nat} {it : Span} (h : itemAt bs pos stop = some it) :
    it.Found bs pos stop := by
  unfold itemAt at h
  split at h
  · rename_i hb
    cases hd : decodeHead (window bs pos stop) with
    | none => simp [hd] at h
    | some hh =>
      rw [hd] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨hsz, hpos, hl⟩ := decodeHead_size hd
      rw [window_length hb.1] at hsz
      have hps := hb.2
      have he := encodeItem_decodeHead hd
      rw [payload_eq_window, take_eq_window, window_window _ (by omega),
        window_window _ (by omega), Nat.add_zero] at he
      simp only [Head.size, Span.Found] at hsz hpos he ⊢
      refine ⟨by simp, ?_, ?_, ?_, ?_, hb.1, fun h => ?_, he⟩
      · omega
      · omega
      · omega
      · omega
      · have := hl h; omega
  · contradiction

theorem itemsF_spans : ∀ (n : Nat) (bs : Bytes) (p stop : Nat) (its : List Span),
    itemsF n bs p stop = some its → p ≤ stop →
      (∀ it ∈ its, p ≤ it.pos ∧ it.stop ≤ stop ∧ itemAt bs it.pos stop = some it) ∧
      ((its.map fun it => window bs it.pos it.stop).flatten = window bs p stop)
  | 0, _, _, _, _, h, _ => by simp [itemsF] at h
  | n + 1, bs, p, stop, its, h, hp => by
    simp only [itemsF] at h
    split at h
    · rename_i hlt
      cases hi : itemAt bs p stop with
      | none => simp [hi] at h
      | some it =>
        rw [hi] at h
        simp only at h
        cases hr : itemsF n bs it.stop stop with
        | none => simp [hr] at h
        | some rest =>
          rw [hr] at h
          cases h
          obtain ⟨hpos, -, -, hlt', hst, hlen, -, -⟩ := itemAt_span hi
          obtain ⟨h1, h2⟩ := itemsF_spans n bs it.stop stop rest hr hst
          refine ⟨?_, ?_⟩
          · intro x hx
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact ⟨by omega, hst, hpos ▸ hi⟩
            · obtain ⟨h1a, h1b, h1c⟩ := h1 x hx; exact ⟨by omega, h1b, h1c⟩
          · simp only [List.map_cons, List.flatten_cons, h2, hpos]
            exact window_append bs (by omega) hst
    · rename_i hge
      cases h
      have : p = stop := by omega
      subst this
      simp [window]

/-- The items of a list payload: each the canonical encoding of its payload, read where the
one before it ends, all of them spanning the payload exactly. -/
theorem itemsAt_spans {bs : Bytes} {start stop : Nat} {its : List Span}
    (h : itemsAt bs start stop = some its) :
    (∀ it ∈ its, start ≤ it.pos ∧ it.stop ≤ stop ∧ itemAt bs it.pos stop = some it) ∧
      (its.map fun it => window bs it.pos it.stop).flatten = window bs start stop := by
  unfold itemsAt at h
  split at h
  · rename_i hb
    exact itemsF_spans _ bs start stop its h hb.1
  · contradiction

/-- Enough fuel is enough: every item takes at least one byte. -/
theorem itemsF_fuel : ∀ (n m : Nat) (bs : Bytes) (p stop : Nat), stop - p < n → stop - p < m →
    itemsF n bs p stop = itemsF m bs p stop
  | 0, _, _, _, _, h, _ => by omega
  | _ + 1, 0, _, _, _, _, h => by omega
  | n + 1, m + 1, bs, p, stop, hn, hm => by
    simp only [itemsF]
    split
    · rename_i hlt
      cases hi : itemAt bs p stop with
      | none => rfl
      | some it =>
        simp only
        obtain ⟨-, -, -, hlt', hst, -⟩ := itemAt_span hi
        rw [itemsF_fuel n m bs it.stop stop (by omega) (by omega)]
    · rfl

theorem itemsF_succ {bs : Bytes} {p stop : Nat} {it : Span} (hp : p < stop)
    (hi : itemAt bs p stop = some it) :
    itemsF (stop - p + 1) bs p stop = (itemsF (stop - it.stop + 1) bs it.stop stop).map (it :: ·) := by
  obtain ⟨-, -, -, hlt', hst, -⟩ := itemAt_span hi
  have : itemsF (stop - p + 1) bs p stop = (itemsF (stop - p) bs it.stop stop).map (it :: ·) := by
    simp only [itemsF, if_pos hp, hi]
  rw [this, itemsF_fuel (stop - p) (stop - it.stop + 1) bs it.stop stop (by omega) (by omega)]

theorem itemsF_none {bs : Bytes} {p stop : Nat} (hp : p < stop) (hi : itemAt bs p stop = none) :
    itemsF (stop - p + 1) bs p stop = none := by
  simp only [itemsF, if_pos hp, hi]

theorem itemsF_stop (bs : Bytes) (p : Nat) : itemsF 1 bs p p = some [] := by
  simp [itemsF]

/-- An encoding at a position is read back: its payload, and where it ends. -/
theorem itemAt_encodeItem {bs e r p : Bytes} {pos stop : Nat} {l : Bool}
    (he : encodeItem l p = some e) (hs : stop ≤ bs.length) (hw : window bs pos stop = e ++ r) :
    itemAt bs pos stop = some ⟨l, pos, pos + (e.length - p.length), pos + e.length⟩ := by
  have hne : e ≠ [] := by
    cases l with
    | false => exact encodeTree_ne_nil (t := .leaf p) he
    | true =>
      have := encodeList_length he
      intro h; rw [h] at this; simp at this
  have hpos : pos < stop := by
    have := congrArg List.length hw
    rw [window_length hs, List.length_append] at this
    have := List.length_pos_iff.mpr hne
    omega
  have hle := (encodeItem_suffix he).1
  unfold itemAt
  rw [if_pos ⟨hs, hpos⟩, hw, decodeHead_encodeItem he r]
  simp only [Option.map_some, Head.size]
  congr 2
  omega

/-! ## Reading inside a window -/

/-- An item found `k` bytes further on. -/
def Span.shift (k : Nat) (it : Span) : Span := ⟨it.list, it.pos + k, it.start + k, it.stop + k⟩

/-- Reading an item depends only on the bytes it reads: inside a window `[s, e)` of `bs`, the
item at `p` is the item at `p - s` of the window, `s` bytes further on. -/
theorem itemAt_window (bs : Bytes) {s e p q : Nat} (h1 : s ≤ p) (h2 : q ≤ e)
    (h3 : e ≤ bs.length) :
    itemAt bs p q = (itemAt (window bs s e) (p - s) (q - s)).map (Span.shift s) := by
  unfold itemAt
  have hwl : (window bs s e).length = e - s := window_length h3
  by_cases hc : q ≤ bs.length ∧ p < q
  · rw [if_pos hc, if_pos ⟨by omega, by omega⟩, window_window _ (by omega),
      show s + (p - s) = p by omega, show s + (q - s) = q by omega, Option.map_map]
    congr 1
    funext h
    simp only [Function.comp_apply, Span.shift, Span.mk.injEq, true_and]
    omega
  · rw [if_neg hc, if_neg (by omega)]
    rfl

theorem itemsF_window (bs : Bytes) {s e : Nat} (h3 : e ≤ bs.length) : ∀ (n : Nat) (p q : Nat),
    s ≤ p → q ≤ e →
    itemsF n bs p q = (itemsF n (window bs s e) (p - s) (q - s)).map (List.map (Span.shift s))
  | 0, _, _, _, _ => rfl
  | n + 1, p, q, h1, h2 => by
    simp only [itemsF]
    by_cases hpq : p < q
    · rw [if_pos hpq, if_pos (by omega), itemAt_window bs h1 h2 h3]
      cases hi : itemAt (window bs s e) (p - s) (q - s) with
      | none => rfl
      | some it =>
        simp only [Option.map_some]
        obtain ⟨hp, -, -, hlt, hst, -⟩ := itemAt_span hi
        rw [itemsF_window bs (s := s) h3 n (Span.shift s it).stop q (by simp [Span.shift]) h2]
        rw [show (Span.shift s it).stop - s = it.stop by simp [Span.shift]]
        cases itemsF n (window bs s e) it.stop (q - s) with
        | none => rfl
        | some l => rfl
    · rw [if_neg hpq, if_neg (by omega)]
      rfl

/-- The items of a payload inside a window are the window's, shifted. -/
theorem itemsAt_window (bs : Bytes) {s e a b : Nat} (h1 : s ≤ a) (hab : a ≤ b) (h2 : b ≤ e)
    (h3 : e ≤ bs.length) :
    itemsAt bs a b = (itemsAt (window bs s e) (a - s) (b - s)).map (List.map (Span.shift s)) := by
  unfold itemsAt
  have hwl : (window bs s e).length = e - s := window_length h3
  by_cases hc : a ≤ b ∧ b ≤ bs.length
  · rw [if_pos hc, if_pos ⟨by omega, by omega⟩, show b - s - (a - s) + 1 = b - a + 1 by omega]
    exact itemsF_window bs h3 _ a b h1 h2
  · rw [if_neg hc, if_neg (by omega)]
    rfl

/-! ## Over a `ByteArray`: what runs

The reader above copies a `window` of a list for each item, so reading `n` items costs `n²`
(compiled, 16,000 one-byte items take close to a second). `itemAtB` and `itemsAtB` read the
same items in place, from a `ByteArray`: a head reads at most nine bytes, by index, and the walk
over a list's items runs in constant stack (a million items in 22 ms, in a 256 KiB stack). They
are `itemAt` and `itemsAt` of the same bytes (`itemAtB_eq`, `itemsAtB_eq`). -/

open LeanLight.Lc.Bytes (byteAt byteAt_eq size_eq)

/-- `short`, given the number of bytes after the first, `size`, and the first of them, `b1`. -/
def shortH (list : Bool) (len size : Nat) (b1 : UInt8) : Option Head :=
  if len ≤ size ∧ ¬(list = false ∧ len = 1 ∧ b1.toNat < 128) then some ⟨list, 1, len⟩
  else none

/-- `long`, given `size` and `b1` as `shortH` is, and the big-endian value `v` of the `n` length
bytes. -/
def longH (list : Bool) (n size : Nat) (b1 : UInt8) (v : Nat) : Option Head :=
  if n ≤ size ∧ b1 ≠ 0 ∧ 56 ≤ v ∧ v ≤ size - n then some ⟨list, 1 + n, v⟩ else none

/-- `decodeHead` of an item whose first byte is `b`, followed by `size` bytes, the first of them
`b1`, whose first `n` bytes have the big-endian value `v n`. -/
@[inline] def headOf (b : UInt8) (size : Nat) (b1 : UInt8) (v : Nat → Nat) : Option Head :=
  if b.toNat < 128 then some ⟨false, 0, 1⟩
  else if b.toNat < 184 then shortH false (b.toNat - 128) size b1
  else if b.toNat < 192 then longH false (b.toNat - 183) size b1 (v (b.toNat - 183))
  else if b.toNat < 248 then shortH true (b.toNat - 192) size b1
  else longH true (b.toNat - 247) size b1 (v (b.toNat - 247))

theorem decodeHead_cons (b : UInt8) (rest : Bytes) :
    decodeHead (b :: rest) =
      headOf b rest.length (rest[0]?.getD 0) (fun n => beValue (rest.take n)) := rfl

/-- `headOf` reads `v n` only for a length `n` the bytes hold. -/
theorem headOf_congr {b : UInt8} {size : Nat} {b1 : UInt8} {v v' : Nat → Nat}
    (h : ∀ n, n ≤ size → v n = v' n) : headOf b size b1 v = headOf b size b1 v' := by
  have hl : ∀ (list : Bool) (n : Nat),
      longH list n size b1 (v n) = longH list n size b1 (v' n) := by
    intro list n
    unfold longH
    by_cases hn : n ≤ size
    · rw [h n hn]
    · rw [if_neg (fun c => hn c.1), if_neg (fun c => hn c.1)]
  simp only [headOf, hl]

/-- The big-endian value of the `n` bytes of `bs` from `i`, after `acc`: `acc` shifted left by
`n` bytes, plus their value. -/
def beValueB (bs : ByteArray) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | n + 1, i, acc => beValueB bs n (i + 1) (acc * 256 + (byteAt bs i).toNat)

/-- `decodeHead` of the bytes of `bs` from `pos` up to `stop`, read in place. -/
def decodeHeadB (bs : ByteArray) (pos stop : Nat) : Option Head :=
  if pos < stop then
    headOf (byteAt bs pos) (stop - pos - 1) (if pos + 1 < stop then byteAt bs (pos + 1) else 0)
      (fun n => beValueB bs n (pos + 1) 0)
  else none

/-- The item at `pos` of `bs`, read no further than `stop`: `itemAt`, in place
(`itemAtB_eq`). -/
def itemAtB (bs : ByteArray) (pos stop : Nat) : Option Span :=
  if stop ≤ bs.size ∧ pos < stop then
    (decodeHeadB bs pos stop).map fun h => ⟨h.list, pos, pos + h.offset, pos + h.size⟩
  else none

/-- The items from `p` up to `stop`, gathered newest first in `acc`, in constant stack. `n` is
fuel. -/
def itemsAccB (bs : ByteArray) : Nat → Nat → Nat → List Span → Option (List Span)
  | 0, _, _, _ => none
  | n + 1, p, stop, acc =>
    if p < stop then
      match itemAtB bs p stop with
      | none => none
      | some it => itemsAccB bs n it.stop stop (it :: acc)
    else some acc.reverse

/-- The items of the list payload of `bs` from `start` up to `stop`: `itemsAt`, in place
(`itemsAtB_eq`). -/
def itemsAtB (bs : ByteArray) (start stop : Nat) : Option (List Span) :=
  if start ≤ stop ∧ stop ≤ bs.size then itemsAccB bs (stop - start + 1) start stop [] else none

theorem window_getElem? (l : Bytes) (a b i : Nat) :
    (window l a b)[i]? = if a + i < b then l[a + i]? else none := by
  simp only [window, List.getElem?_drop, List.getElem?_take]

theorem window_cons {l : Bytes} {a b : Nat} (h : a < b) (hb : b ≤ l.length) :
    window l a b = (l[a]?.getD 0) :: window l (a + 1) b := by
  apply List.ext_getElem?
  intro i
  cases i with
  | zero =>
    rw [window_getElem?, if_pos (by omega), Nat.add_zero, List.getElem?_eq_getElem (by omega)]
    rfl
  | succ i =>
    rw [window_getElem?, List.getElem?_cons_succ, window_getElem?,
      show a + (i + 1) = a + 1 + i by omega]

theorem window_empty (l : Bytes) {a b : Nat} (h : b ≤ a) : window l a b = [] := by
  apply List.eq_nil_of_length_eq_zero
  simp [window]
  omega

theorem beValueB_eq (bs : ByteArray) : ∀ (n i acc : Nat), i + n ≤ bs.size →
    beValueB bs n i acc =
      (window bs.data.toList i (i + n)).foldl (fun acc b => acc * 256 + b.toNat) acc
  | 0, i, acc, _ => by rw [window_empty _ (by omega)]; rfl
  | n + 1, i, acc, h => by
    rw [window_cons (by omega) (by rw [size_eq]; exact h), List.foldl_cons, ← byteAt_eq,
      show i + (n + 1) = i + 1 + n by omega]
    exact beValueB_eq bs n (i + 1) _ (by omega)

/-- `decodeHeadB` reads what `decodeHead` reads from the window. -/
theorem decodeHeadB_eq {bs : ByteArray} {pos stop : Nat} (h : stop ≤ bs.size) :
    decodeHeadB bs pos stop = decodeHead (window bs.data.toList pos stop) := by
  unfold decodeHeadB
  by_cases hp : pos < stop
  · have hl : stop ≤ bs.data.toList.length := by rw [size_eq]; exact h
    rw [if_pos hp, window_cons hp hl, decodeHead_cons, ← byteAt_eq, window_length hl,
      window_getElem?, Nat.add_zero, show stop - (pos + 1) = stop - pos - 1 by omega]
    have hb1 : (if pos + 1 < stop then bs.data.toList[pos + 1]? else none).getD 0 =
        (if pos + 1 < stop then byteAt bs (pos + 1) else 0) := by
      split
      · rw [byteAt_eq]
      · rfl
    rw [hb1]
    apply headOf_congr
    intro n hn
    rw [take_eq_window, window_window _ (by omega), Nat.add_zero, beValueB_eq bs n (pos + 1) 0
      (by omega)]
    rfl
  · rw [if_neg hp, window_empty _ (by omega)]
    rfl

theorem itemAtB_eq (bs : ByteArray) (pos stop : Nat) :
    itemAtB bs pos stop = itemAt bs.data.toList pos stop := by
  unfold itemAtB itemAt
  rw [size_eq]
  split
  · rename_i h
    rw [decodeHeadB_eq h.1]
  · rfl

theorem itemsAccB_eq (bs : ByteArray) : ∀ (n p stop : Nat) (acc : List Span),
    itemsAccB bs n p stop acc = itemsAccF n bs.data.toList p stop acc
  | 0, _, _, _ => rfl
  | n + 1, p, stop, acc => by
    simp only [itemsAccB, itemsAccF, itemAtB_eq]
    split
    · cases itemAt bs.data.toList p stop with
      | none => rfl
      | some it => exact itemsAccB_eq bs n it.stop stop (it :: acc)
    · rfl

theorem itemsAtB_eq (bs : ByteArray) (start stop : Nat) :
    itemsAtB bs start stop = itemsAt bs.data.toList start stop := by
  unfold itemsAtB itemsAt
  rw [size_eq, itemsF_eq_acc]
  split
  · exact itemsAccB_eq bs _ start stop []
  · rfl

end LeanLight.Spec.RlpDecode
