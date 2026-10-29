import LeanLight.Ssz.Frame

/-!
# The `/updates` framing is canonical (25a)

What `parseUpdates` accepts is exactly a run of at most 128 chunks, each
`u64le(4 + |ssz|) ‖ digest ‖ ssz` with a 4-byte digest: the answer is `encodeUpdates` of the
chunks it returns (`parseUpdates_sound`). So each chunk's length counts its digest, no byte is
left over, and two different chunk lists are never read from one answer. That every such run is
accepted is checked by the vector tests (`LcTest`), not proved here.

netd's re-encoded chunks (LC6, `u64le(1 + |ssz|) ‖ fork ‖ ssz`, the channel's `Updates`
response of form `1`) are proved both ways: what `parseForkUpdates` accepts is
`encodeForkUpdates` of the chunks it returns, each with a fork byte of at most 2
(`parseForkUpdates_sound`), and every run of at most 128 such chunks is accepted
(`parseForkUpdates_encode`); so the encoding is injective (`encodeForkUpdates_injective`).
-/

namespace LeanLight.Lc.Ssz

open LeanLight.Lc.Bytes (byteAt)

theorem leBytes_toList (w v : Nat) :
    (leBytes w v).data.toList = (List.range w).map fun i => UInt8.ofNat (v / 256 ^ i % 256) := by
  induction w generalizing v with
  | zero => rfl
  | succ w ih =>
    simp only [leBytes, ByteArray.data_append, Array.toList_append, ih, List.range_succ_eq_map,
      List.map_cons, List.map_map]
    simp only [Nat.pow_zero, Nat.div_one, List.cons_append, List.nil_append]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp, Nat.pow_succ, Nat.div_div_eq_div_mul]
    rw [Nat.mul_comm 256]

/-- The `w` bytes of `bs` from `off`, as a list. -/
def window (bs : ByteArray) (off w : Nat) : List UInt8 := (bs.data.toList.drop off).take w

theorem readLE_digit (bs : ByteArray) (off w i : Nat) (hi : i < w) :
    readLE bs off w / 256 ^ i % 256 = (byteAt bs (off + i)).toNat := by
  induction w generalizing off i with
  | zero => omega
  | succ w ih =>
    simp only [readLE]
    have hb := (byteAt bs off).toNat_lt
    cases i with
    | zero => simp <;> omega
    | succ i =>
      rw [Nat.pow_succ, Nat.mul_comm (256 ^ i), ← Nat.div_div_eq_div_mul]
      rw [show ((byteAt bs off).toNat + 256 * readLE bs (off + 1) w) / 256 = readLE bs (off + 1) w by
        omega]
      rw [ih (off + 1) i (by omega), Nat.add_assoc, Nat.add_comm 1 i]

/-- A little-endian integer read from `bs`, written back, is the bytes it was read from. -/
theorem leBytes_readLE (bs : ByteArray) (off w : Nat) (h : off + w ≤ bs.size) :
    (leBytes w (readLE bs off w)).data.toList = window bs off w := by
  rw [leBytes_toList]
  apply List.ext_getElem
  · simp [window]; omega
  · intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_range, window, List.getElem_take, List.getElem_drop]
    rw [readLE_digit bs off w i (by simpa using h₁)]
    simp only [byteAt, UInt8.ofNat_toNat]
    rw [getElem?_pos bs (off + i) (by simp at h₁; omega)]
    rfl

theorem encodeUpdates_toList (cs : List Chunk) :
    (encodeUpdates cs).data.toList = cs.flatMap fun c => c.bytes.data.toList := by
  suffices ∀ (acc : ByteArray), (cs.foldl (fun acc c => acc ++ c.bytes) acc).data.toList =
      acc.data.toList ++ cs.flatMap fun c => c.bytes.data.toList by
    simpa [encodeUpdates] using this .empty
  induction cs with
  | nil => simp
  | cons c cs ih => intro acc; simp [ih, List.append_assoc]

theorem take_drop_append {α : Type} (l : List α) (a n : Nat) :
    (l.drop a).take n ++ l.drop (a + n) = l.drop a := by
  rw [← List.drop_drop]
  exact List.take_append_drop n (l.drop a)

theorem extract_toList (bs : ByteArray) (a b : Nat) :
    (Bytes.extract bs a b).data.toList = (bs.data.toList.take b).drop a := Bytes.extract_eq bs a b

/-- The invariant of `parseChunks`: what it returns is `acc` and chunks whose bytes are the rest
of the answer, at most `fuel` of them, each with a 4-byte digest. -/
theorem parseChunks_sound (bs : ByteArray) :
    ∀ (fuel off : Nat) (acc cs : Array Chunk), off ≤ bs.size →
      parseChunks bs fuel off acc = some cs →
      ∃ rest : List Chunk, cs.toList = acc.toList ++ rest ∧ rest.length ≤ fuel ∧
        (∀ c ∈ rest, c.digest.size = 4) ∧
        (rest.flatMap fun c => c.bytes.data.toList) = bs.data.toList.drop off
  | fuel, off, acc, cs, hoff, h => by
    unfold parseChunks at h
    split at h
    · rename_i hend
      cases h
      exact ⟨[], by simp, by simp, by simp, by simp [hend]⟩
    · rename_i hend
      match fuel, h with
      | 0, h => simp at h
      | fuel + 1, h =>
        simp only at h
        split at h
        · rename_i hlen
          obtain ⟨h4, hfit⟩ := hlen
          obtain ⟨rest, hcs, hl, hd, hb⟩ :=
            parseChunks_sound bs fuel _ _ cs (by omega) h
          refine ⟨⟨Bytes.extract bs (off + 8) (off + 12),
            Bytes.extract bs (off + 12) (off + 8 + readLE bs off 8)⟩ :: rest,
            by simp [hcs], by simp; omega, ?_, ?_⟩
          · intro c hc
            rcases List.mem_cons.mp hc with rfl | hc
            · simp [Bytes.extract]; omega
            · exact hd c hc
          · rw [List.flatMap_cons, hb]
            simp only [Chunk.bytes, ByteArray.data_append, Array.toList_append, extract_toList]
            have hsz : (Bytes.extract bs (off + 12) (off + 8 + readLE bs off 8)).size =
                readLE bs off 8 - 4 := by simp [Bytes.extract]; omega
            rw [hsz, show 4 + (readLE bs off 8 - 4) = readLE bs off 8 by omega,
              leBytes_readLE bs off 8 (by omega)]
            simp only [window, List.drop_take, List.append_assoc]
            have e₁ : off + 12 - (off + 8) = 4 := by omega
            have e₂ : off + 8 + readLE bs off 8 - (off + 12) = readLE bs off 8 - 4 := by omega
            rw [e₁, e₂, show off + 8 + readLE bs off 8 = off + 12 + (readLE bs off 8 - 4) by omega,
              take_drop_append, show off + 12 = off + 8 + 4 by omega, take_drop_append,
              take_drop_append]
        · simp at h

/-- **Framing.** An `/updates` answer `parseUpdates` accepts is exactly `encodeUpdates` of the
chunks it returns, at most 128 of them, each with a 4-byte digest: every chunk's length field is
4 plus its SSZ's length (`Chunk.bytes`), and no byte is left over. -/
theorem parseUpdates_sound {bs : ByteArray} {cs : Array Chunk} (h : parseUpdates bs = some cs) :
    encodeUpdates cs.toList = bs ∧ cs.size ≤ maxRequestUpdates ∧ ∀ c ∈ cs, c.digest.size = 4 := by
  obtain ⟨rest, hcs, hl, hd, hb⟩ := parseChunks_sound bs _ 0 #[] cs (Nat.zero_le _) h
  simp only [List.nil_append] at hcs
  refine ⟨?_, ?_, ?_⟩
  · apply ByteArray.ext
    apply Array.toList_inj.mp
    rw [encodeUpdates_toList, hcs, hb, List.drop_zero]
  · rw [← Array.length_toList, hcs]; exact hl
  · intro c hc
    exact hd c (by rw [← hcs]; exact Array.mem_toList_iff.mpr hc)

/-! ## Re-encoded chunks (LC6) -/

theorem forkChunk_toList (c : ForkChunk) :
    c.bytes.data.toList = (leBytes 8 (1 + c.ssz.size)).data.toList ++ c.fork :: c.ssz.data.toList := by
  simp [ForkChunk.bytes]

theorem leBytes_length (w v : Nat) : (leBytes w v).data.toList.length = w := by
  simp [leBytes_toList]

theorem encodeForkUpdates_toList (cs : List ForkChunk) :
    (encodeForkUpdates cs).data.toList = cs.flatMap fun c => c.bytes.data.toList := by
  suffices ∀ (acc : ByteArray), (cs.foldl (fun acc c => acc ++ c.bytes) acc).data.toList =
      acc.data.toList ++ cs.flatMap fun c => c.bytes.data.toList by
    simpa [encodeForkUpdates] using this .empty
  induction cs with
  | nil => simp
  | cons c cs ih => intro acc; simp [ih, List.append_assoc]

/-- The invariant of `parseForkChunks`: what it returns is `acc` and chunks whose bytes are the
rest of the answer, at most `fuel` of them, each with a fork byte of at most 2. -/
theorem parseForkChunks_sound (bs : ByteArray) :
    ∀ (fuel off : Nat) (acc cs : Array ForkChunk), off ≤ bs.size →
      parseForkChunks bs fuel off acc = some cs →
      ∃ rest : List ForkChunk, cs.toList = acc.toList ++ rest ∧ rest.length ≤ fuel ∧
        (∀ c ∈ rest, c.fork ≤ 2) ∧
        (rest.flatMap fun c => c.bytes.data.toList) = bs.data.toList.drop off
  | fuel, off, acc, cs, hoff, h => by
    unfold parseForkChunks at h
    split at h
    · rename_i hend
      cases h
      exact ⟨[], by simp, by simp, by simp, by simp [hend]⟩
    · rename_i hend
      match fuel, h with
      | 0, h => simp at h
      | fuel + 1, h =>
        simp only at h
        split at h
        · rename_i hlen
          obtain ⟨h1, hfit, hf⟩ := hlen
          obtain ⟨rest, hcs, hl, hd, hb⟩ :=
            parseForkChunks_sound bs fuel _ _ cs (by omega) h
          refine ⟨⟨byteAt bs (off + 8),
            Bytes.extract bs (off + 9) (off + 8 + readLE bs off 8)⟩ :: rest,
            by simp [hcs], by simp; omega, ?_, ?_⟩
          · intro c hc
            rcases List.mem_cons.mp hc with rfl | hc
            · exact hf
            · exact hd c hc
          · rw [List.flatMap_cons, hb, forkChunk_toList]
            have hsz : (Bytes.extract bs (off + 9) (off + 8 + readLE bs off 8)).size =
                readLE bs off 8 - 1 := by simp [Bytes.extract]; omega
            rw [hsz, show 1 + (readLE bs off 8 - 1) = readLE bs off 8 by omega,
              leBytes_readLE bs off 8 (by omega), extract_toList]
            have hbyte : byteAt bs (off + 8) :: bs.data.toList.drop (off + 9) =
                bs.data.toList.drop (off + 8) := by
              rw [Bytes.byteAt_eq, List.getElem?_eq_getElem (by simp; omega), Option.getD_some,
                ← List.drop_eq_getElem_cons]
            simp only [window, List.drop_take]
            rw [show off + 8 + readLE bs off 8 - (off + 9) = readLE bs off 8 - 1 by omega,
              show off + 8 + readLE bs off 8 = off + 9 + (readLE bs off 8 - 1) by omega,
              List.append_assoc, List.cons_append, take_drop_append, hbyte, take_drop_append]
        · simp at h

/-- **Framing, re-encoded.** A re-encoded `/updates` answer `parseForkUpdates` accepts is exactly
`encodeForkUpdates` of the chunks it returns, at most 128 of them, each with a fork byte of at
most 2: every chunk's length field is 1 plus its SSZ's length, and no byte is left over. -/
theorem parseForkUpdates_sound {bs : ByteArray} {cs : Array ForkChunk}
    (h : parseForkUpdates bs = some cs) :
    encodeForkUpdates cs.toList = bs ∧ cs.size ≤ maxRequestUpdates ∧ ∀ c ∈ cs, c.fork ≤ 2 := by
  obtain ⟨rest, hcs, hl, hd, hb⟩ := parseForkChunks_sound bs _ 0 #[] cs (Nat.zero_le _) h
  simp only [List.nil_append] at hcs
  refine ⟨?_, ?_, ?_⟩
  · apply ByteArray.ext
    apply Array.toList_inj.mp
    rw [encodeForkUpdates_toList, hcs, hb, List.drop_zero]
  · rw [← Array.length_toList, hcs]; exact hl
  · intro c hc
    exact hd c (by rw [← hcs]; exact Array.mem_toList_iff.mpr hc)

theorem readLE_of_bytes (bs : ByteArray) (w : Nat) :
    ∀ (off v : Nat), (∀ i < w, byteAt bs (off + i) = UInt8.ofNat (v / 256 ^ i % 256)) →
      readLE bs off w = v % 256 ^ w := by
  induction w with
  | zero => intro off v _; simp [readLE, Nat.mod_one]
  | succ w ih =>
    intro off v h
    simp only [readLE]
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero, Nat.pow_zero, Nat.div_one] at h0
    have hr := ih (off + 1) (v / 256) (fun i hi => by
      have := h (i + 1) (by omega)
      rw [show off + (i + 1) = off + 1 + i by omega, Nat.pow_succ, Nat.mul_comm (256 ^ i),
        ← Nat.div_div_eq_div_mul] at this
      exact this)
    rw [h0, hr, Nat.pow_succ, Nat.mul_comm (256 ^ w) 256, Nat.mod_mul]
    simp

theorem byteAt_drop (bs : ByteArray) (off i : Nat) :
    byteAt bs (off + i) = (bs.data.toList.drop off)[i]?.getD 0 := by
  rw [Bytes.byteAt_eq, List.getElem?_drop]

/-- The invariant of `parseForkChunks`, the other way: from `off`, where the rest of the answer
is the bytes of `cs`, it reads `cs`. -/
theorem parseForkChunks_complete (bs : ByteArray) :
    ∀ (cs : List ForkChunk) (fuel off : Nat) (acc : Array ForkChunk),
      cs.length ≤ fuel → off ≤ bs.size → (∀ c ∈ cs, c.fork ≤ 2 ∧ 1 + c.ssz.size < 2 ^ 64) →
      bs.data.toList.drop off = cs.flatMap (fun c => c.bytes.data.toList) →
      parseForkChunks bs fuel off acc = some (acc ++ cs.toArray)
  | [], fuel, off, acc, _, hoff, _, h => by
    unfold parseForkChunks
    have : bs.size ≤ off := by
      have := congrArg List.length h
      simp at this; omega
    simp [show off = bs.size by omega]
  | c :: cs, fuel, off, acc, hl, hoff, hc, h => by
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hl; omega⟩
    obtain ⟨hf, hs⟩ := hc c List.mem_cons_self
    rw [List.flatMap_cons, forkChunk_toList, List.append_assoc] at h
    have hlb := leBytes_length 8 (1 + c.ssz.size)
    have hlen : off + 9 + c.ssz.size ≤ bs.size := by
      have := congrArg List.length h
      simp only [List.length_drop, List.length_append, List.length_cons, hlb,
        Array.length_toList, ByteArray.size_data] at this
      omega
    have hread : readLE bs off 8 = 1 + c.ssz.size := by
      rw [readLE_of_bytes bs 8 off (1 + c.ssz.size), Nat.mod_eq_of_lt (by omega)]
      intro i hi
      rw [byteAt_drop, h, List.getElem?_append_left (by omega), leBytes_toList]
      simp [hi]
    have hfork : byteAt bs (off + 8) = c.fork := by
      rw [byteAt_drop, h, List.getElem?_append_right (by omega), hlb]
      simp
    have hrest : bs.data.toList.drop (off + 9) = c.ssz.data.toList ++
        cs.flatMap (fun c => c.bytes.data.toList) := by
      rw [← List.drop_drop, h, show 9 = (leBytes 8 (1 + c.ssz.size)).data.toList.length + 1 by
        omega, List.drop_append]
      simp
    have hssz : Bytes.extract bs (off + 9) (off + 8 + (1 + c.ssz.size)) = c.ssz := by
      apply ByteArray.ext; apply Array.toList_inj.mp
      rw [extract_toList, List.drop_take, show off + 8 + (1 + c.ssz.size) - (off + 9) =
        c.ssz.size by omega, hrest, List.take_append_of_le_length (by simp),
        List.take_of_length_le (by simp)]
    have hnext : bs.data.toList.drop (off + 8 + (1 + c.ssz.size)) =
        cs.flatMap (fun c => c.bytes.data.toList) := by
      rw [show off + 8 + (1 + c.ssz.size) = off + 9 + c.ssz.size by omega, ← List.drop_drop,
        hrest, List.drop_left' (by simp)]
    unfold parseForkChunks
    rw [if_neg (by omega)]
    simp only
    rw [hread, if_pos ⟨by omega, by omega, by rw [hfork]; exact hf⟩, hfork, hssz]
    rw [parseForkChunks_complete bs cs fuel _ _ (by simp at hl; omega) (by omega)
      (fun x hx => hc x (List.mem_cons_of_mem _ hx)) hnext]
    simp

/-- **Re-encoded chunks are accepted.** Every run of at most 128 chunks, each with a fork byte
of at most 2 and an SSZ shorter than `2 ^ 64 - 1` bytes, is read back by `parseForkUpdates`. -/
theorem parseForkUpdates_encode (cs : List ForkChunk) (hl : cs.length ≤ maxRequestUpdates)
    (hc : ∀ c ∈ cs, c.fork ≤ 2 ∧ 1 + c.ssz.size < 2 ^ 64) :
    parseForkUpdates (encodeForkUpdates cs) = some cs.toArray := by
  unfold parseForkUpdates
  rw [parseForkChunks_complete _ cs _ 0 #[] hl (Nat.zero_le _) hc
    (by rw [List.drop_zero, encodeForkUpdates_toList])]
  simp

/-- A re-encoded chunk of fork 2 (Gloas) and SSZ `aa bb` is `03 00 00 00 00 00 00 00 02 aa bb`. -/
theorem layout_forkChunk :
    (ForkChunk.bytes ⟨2, ⟨#[0xaa, 0xbb]⟩⟩).data.toList = [3, 0, 0, 0, 0, 0, 0, 0, 2, 0xaa, 0xbb] := by
  decide

/-- One byte string is the encoding of at most one run of re-encoded chunks. -/
theorem encodeForkUpdates_injective {cs cs' : List ForkChunk}
    (hl : cs.length ≤ maxRequestUpdates) (hc : ∀ c ∈ cs, c.fork ≤ 2 ∧ 1 + c.ssz.size < 2 ^ 64)
    (hl' : cs'.length ≤ maxRequestUpdates)
    (hc' : ∀ c ∈ cs', c.fork ≤ 2 ∧ 1 + c.ssz.size < 2 ^ 64)
    (h : encodeForkUpdates cs = encodeForkUpdates cs') : cs = cs' := by
  have e := parseForkUpdates_encode cs hl hc
  rw [h, parseForkUpdates_encode cs' hl' hc'] at e
  simpa using (Option.some.inj e).symm

end LeanLight.Lc.Ssz
