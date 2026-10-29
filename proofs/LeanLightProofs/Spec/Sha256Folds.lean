import LeanLightProofs.Spec.Sha256

/-!
# SHA-256's specification, restated as folds

`Spec.Sha256.sha256`'s loops (VCVio's `do` blocks over ranges, `Vendor/VCVio/Sha2.lean`)
restated as folds over lists, and what the message schedule and the padded message hold where:
`compress_eq` (the schedule `schedW`, the rounds `rounds`, the final addition `addVars`),
`pad_eq`, `sha256_eq`, and `schedW_lt`/`schedW_ge` (each schedule word from the block, or from
the four earlier words it depends on).

They were proved for the refinement of `lkd_verified::sha256` (`Refinement.Sha256`, which
imports this file) and are about the specification alone, so they live here, where a proof that
must not import the extraction can use them: `LeanLightProofs.Sha256` proves the light client's
runtime SHA-256 equal to the specification with them. Their namespace is the one they were
proved in, so no statement or name changed in the move.
-/

namespace LeanLight.Refinement.Sha256

open SLHDSA.Concrete.Sha2 (rotr ch maj bsig0 bsig1 ssig0 ssig1 k iv)

/-! ## The specification's loops, as folds -/

open SLHDSA.Concrete.Sha2 (compress pad stateBytes32 sha256Family u32be u64be)

/-- The first sixteen words of the schedule: big-endian words of the block at `base`. -/
def schedWord (m : ByteArray) (base : Nat) (w : Array UInt32) (t : Nat) : Array UInt32 :=
  w.set! t ((m[base + t * 4]!).toUInt32 <<< 24 ||| (m[base + t * 4 + 1]!).toUInt32 <<< 16 |||
    (m[base + t * 4 + 2]!).toUInt32 <<< 8 ||| (m[base + t * 4 + 3]!).toUInt32)

/-- The other 48 words of the schedule. -/
def schedExpand (w : Array UInt32) (t : Nat) : Array UInt32 :=
  w.set! t (ssig1 (w[t - 2]!) + w[t - 7]! + ssig0 (w[t - 15]!) + w[t - 16]!)

/-- The message schedule W of the block of `m` at `base`. -/
def schedW (m : ByteArray) (base : Nat) : Array UInt32 :=
  (List.range' 16 (64 - 16)).foldl (fun w t => schedExpand w t)
    ((List.range' 0 16).foldl (fun w t => schedWord m base w t) (Array.replicate 64 0))

/--
The eight working variables a … h, as the specification's `do` block threads them:
nested pairs, the type `do` notation uses for several mutable variables.
-/
abbrev Vars := UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32

/-- Builds the working variables from a … h. -/
abbrev vars (a b c d e f g h : UInt32) : Vars := ⟨a, b, c, d, e, f, g, h⟩

/-- One round of the compression. -/
def roundStep (w : Array UInt32) (v : Vars) (t : Nat) : Vars :=
  let t1 := v.2.2.2.2.2.2.2 + bsig1 v.2.2.2.2.1 + ch v.2.2.2.2.1 v.2.2.2.2.2.1 v.2.2.2.2.2.2.1 +
    k[t]! + w[t]!
  let t2 := bsig0 v.1 + maj v.1 v.2.1 v.2.2.1
  ⟨t1 + t2, v.1, v.2.1, v.2.2.1, v.2.2.2.1 + t1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2.1⟩

/-- The 64 rounds from the state `st`. -/
def rounds (st : Array UInt32) (w : Array UInt32) : Vars :=
  (List.range' 0 64).foldl (fun v t => roundStep w v t)
    ⟨st[0]!, st[1]!, st[2]!, st[3]!, st[4]!, st[5]!, st[6]!, st[7]!⟩

/-- The state after adding the rounds' result. -/
def addVars (st : Array UInt32) (v : Vars) : Array UInt32 :=
  #[st[0]! + v.1, st[1]! + v.2.1, st[2]! + v.2.2.1, st[3]! + v.2.2.2.1, st[4]! + v.2.2.2.2.1,
    st[5]! + v.2.2.2.2.2.1, st[6]! + v.2.2.2.2.2.2.1, st[7]! + v.2.2.2.2.2.2.2]

theorem compress_eq (st : Array UInt32) (m : ByteArray) (base : Nat) :
    compress st m base = addVars st (rounds st (schedW m base)) := by
  unfold compress
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, pure_bind,
    List.forIn_pure_yield_eq_foldl, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  simp only [addVars, rounds, schedW, schedWord, schedExpand, roundStep]
  -- The two sides agree term for term; `congr` checks them piecewise, where a plain `rfl`
  -- unfolds the 64-round folds and exhausts the recursion limit.
  congr 1

theorem foldl_push_zero (l : List Nat) (acc : ByteArray) :
    (l.foldl (fun b _ => b.push 0) acc).data.toList = acc.data.toList ++ List.replicate l.length 0 := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih]
    simp only [ByteArray.data_push, Array.toList_push, List.append_assoc, List.length_cons,
      List.singleton_append, ← List.replicate_succ, List.replicate_succ']

/-- The number of zero bytes FIPS 180-4 §5.1.1 puts after `0x80`, for a message of `n` bytes. -/
def padZeros (n : Nat) : Nat := (56 + 64 - (n + 1) % 64) % 64

theorem pad_eq (msg : ByteArray) :
    (pad msg).data.toList = msg.data.toList ++ [0x80] ++ List.replicate (padZeros msg.size) 0 ++
      (u64be (msg.size.toUInt64 * 8)).data.toList := by
  unfold pad
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, pure_bind,
    List.forIn_pure_yield_eq_foldl, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  show (List.foldl (fun b _ => b.push 0) (msg.push 128) _ ++ _).data.toList = _
  rw [ByteArray.data_append, Array.toList_append, foldl_push_zero, List.length_range']
  simp [padZeros]

theorem sha256_eq (msg : ByteArray) :
    Spec.Sha256.sha256 msg = (stateBytes32 ((List.range ((pad msg).size / 64)).foldl
      (fun st b => compress st (pad msg) (b * 64)) iv)).extract 0 32 := by
  unfold Spec.Sha256.sha256 SLHDSA.Concrete.Sha2.sha256 sha256Family
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, pure_bind,
    List.forIn_pure_yield_eq_foldl, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    ← List.range_eq_range']
  rfl

/-! ## Folds that fill an array in order -/

/-- Reading an array after `set!` at another index. -/
theorem set!_getElem!_ne (A : _root_.Array UInt32) (i j : Nat) (v : UInt32) (h : i ≠ j) :
    (A.set! i v)[j]! = A[j]! := by
  rw [Array.set!_eq_setIfInBounds]
  by_cases hj : j < A.size
  · have hj' : j < (A.setIfInBounds i v).size := by simpa using hj
    rw [getElem!_pos (A.setIfInBounds i v) j hj', getElem!_pos A j hj,
      Array.getElem_setIfInBounds_ne hj h]
  · have hj' : ¬j < (A.setIfInBounds i v).size := by simpa using hj
    rw [getElem!_neg (A.setIfInBounds i v) j hj', getElem!_neg A j hj]

/-- Reading an array after `set!` at the same, in-bounds, index. -/
theorem set!_getElem!_self (A : _root_.Array UInt32) (i : Nat) (v : UInt32) (h : i < A.size) :
    (A.set! i v)[i]! = v := by
  rw [Array.set!_eq_setIfInBounds]
  have h' : i < (A.setIfInBounds i v).size := by simpa using h
  rw [getElem!_pos (A.setIfInBounds i v) i h', Array.getElem_setIfInBounds h, if_pos rfl]

/-- The fold that sets index `t` to `g w t`, for `t` from `a` on, `n` times. -/
abbrev fill (g : _root_.Array UInt32 → Nat → UInt32) (A : _root_.Array UInt32) (a n : Nat) :
    _root_.Array UInt32 :=
  (List.range' a n).foldl (fun w t => w.set! t (g w t)) A

theorem fill_succ (g : _root_.Array UInt32 → Nat → UInt32) (A : _root_.Array UInt32) (a n : Nat) :
    fill g A a (n + 1) = (fill g A a n).set! (a + n) (g (fill g A a n) (a + n)) := by
  simp only [fill, List.range'_concat, Nat.one_mul, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

theorem fill_add (g : _root_.Array UInt32 → Nat → UInt32) (A : _root_.Array UInt32) (a m n : Nat) :
    fill g A a (m + n) = fill g (fill g A a m) (a + m) n := by
  simp only [fill, ← List.range'_append, List.foldl_append, Nat.one_mul]

theorem fill_size (g : _root_.Array UInt32 → Nat → UInt32) (A : _root_.Array UInt32) (a n : Nat) :
    (fill g A a n).size = A.size := by
  induction n with
  | zero => rfl
  | succ n ih => rw [fill_succ, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, ih]

/-- Indices below the start are left alone. -/
theorem fill_getElem!_of_lt (g : _root_.Array UInt32 → Nat → UInt32) (A : _root_.Array UInt32)
    (a n i : Nat) (h : i < a) : (fill g A a n)[i]! = A[i]! := by
  induction n with
  | zero => rfl
  | succ n ih => rw [fill_succ, set!_getElem!_ne _ _ _ _ (by omega), ih]

/-- Once set, an index keeps its value: later steps write only above it. -/
theorem fill_getElem!_stable (g : _root_.Array UInt32 → Nat → UInt32) (A : _root_.Array UInt32)
    (a m n i : Nat) (h : i < a + m) (hmn : m ≤ n) : (fill g A a n)[i]! = (fill g A a m)[i]! := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [fill_add, fill_getElem!_of_lt _ _ _ _ _ h]

/-- What a fill writes at index `i`: `g` of the array as it was just before. -/
theorem fill_getElem!_self (g : _root_.Array UInt32 → Nat → UInt32) (A : _root_.Array UInt32)
    (a n i : Nat) (ha : a ≤ i) (hi : i < a + n) (hs : i < A.size) :
    (fill g A a n)[i]! = g (fill g A a (i - a)) i := by
  rw [fill_getElem!_stable g A a (i - a + 1) n i (by omega) (by omega), fill_succ,
    show a + (i - a) = i by omega, set!_getElem!_self _ _ _ (by rw [fill_size]; exact hs)]

/-! ## The message schedule -/

/-- The big-endian word of `m` at byte `o`. -/
def beWord (m : ByteArray) (o : Nat) : UInt32 :=
  (m[o]!).toUInt32 <<< 24 ||| (m[o + 1]!).toUInt32 <<< 16 ||| (m[o + 2]!).toUInt32 <<< 8 |||
    (m[o + 3]!).toUInt32

/-- Schedule word `t ≥ 16`, from the four earlier words it depends on. -/
def expandAt (w : _root_.Array UInt32) (t : Nat) : UInt32 :=
  ssig1 (w[t - 2]!) + w[t - 7]! + ssig0 (w[t - 15]!) + w[t - 16]!

theorem schedW_fill (m : ByteArray) (base : Nat) :
    schedW m base = fill expandAt (fill (fun _ t => beWord m (base + t * 4))
      (_root_.Array.replicate 64 0) 0 16) 16 48 := rfl

theorem schedW_lt (m : ByteArray) (base t : Nat) (h : t < 16) :
    (schedW m base)[t]! = beWord m (base + t * 4) := by
  rw [schedW_fill, fill_getElem!_of_lt _ _ _ _ _ h,
    fill_getElem!_self _ _ _ _ _ (Nat.zero_le _) (by omega) (by simp; omega)]

theorem schedW_ge (m : ByteArray) (base t : Nat) (h16 : 16 ≤ t) (h : t < 64) :
    (schedW m base)[t]! = expandAt (schedW m base) t := by
  rw [schedW_fill, fill_getElem!_self _ _ _ _ _ h16 (by omega) (by rw [fill_size]; simp; omega)]
  simp only [expandAt]
  rw [fill_getElem!_stable _ _ 16 (t - 16) 48 (t - 2) (by omega) (by omega),
    fill_getElem!_stable _ _ 16 (t - 16) 48 (t - 7) (by omega) (by omega),
    fill_getElem!_stable _ _ 16 (t - 16) 48 (t - 15) (by omega) (by omega),
    fill_getElem!_stable _ _ 16 (t - 16) 48 (t - 16) (by omega) (by omega)]

end LeanLight.Refinement.Sha256
