import LeanLightProofs.Bls.EthCurves
import LeanLightProofs.Bls.HashCurve
import LeanLightProofs.Vendor.SszSpecs.Ssz.Proofs.Hash.Sha256Laws

/-!
# BLS12-381: the runtime's `hash_to_G2` is EthLib's (25c)

On every input, each step of `LeanLight.Bls.H2C` equals EthLib's readable `HashToCurve`, both hashing
with `Ssz.Sha256.hash` (SHA-256 is never evaluated: its outputs are compared as terms, and only
their size, 32, is used):

* `expandXmd_eq`: `expand_message_xmd` to 256 bytes, the runtime's `expandXmd` is EthLib's
  `expandMessageXmd msg dst 256` (which never errs for that length);
* `hashToField_eq`: `hash_to_field`, two `Fp2` elements, the runtime's read as EthLib's;
* `sqrt?_ofEth`: the runtime's `Fp2.sqrt?` is EthLib's `Fp2.sqrt` (so EthLib's is sound and
  complete too, by `Fp2.sqrt?_some` and `Fp2.sqrt?_isSome_iff`);
* `sswu?_ofEth`: SSWU, `none` exactly when EthLib's `simpleSwu` errs (no root), else its point;
* `isoMap_ofEth`: the 3-isogeny, the runtime's Jacobian triple and EthLib's point stand for the
  same point (both the identity when a denominator vanishes);
* `clearCofactor_ofEth`: both `clear_cofactor`s are `[h_eff]P` on a point of `E'`;
* `hashToG2?_eq_eth`: **`hashToG2?` is EthLib's `hashToG2` read as an affine point**, `none`
  exactly when EthLib errs or returns the identity.

EthLib's private helpers (`i2osp`, `strxor`, `fpFromBytesL`, `sgn0Fp2`) are unfolded by
`delta_private`, and its definitions through `value_eq` (`LeanLightProofs.Bls.ValueEq`).
-/

namespace LeanLight.Lc.Bls

open WeierstrassCurve WeierstrassCurve.Jacobian
open LeanLight.Lc.Bls.Provenance (ofEth)

local notation "aff2" => Point.toAffine E2

/-! ## Bytes -/

theorem byteArray_push_eq_append (b : ByteArray) (x : UInt8) : b.push x = b ++ ⟨#[x]⟩ := by
  apply ByteArray.ext; rw [ByteArray.data_push, ByteArray.data_append, Array.push_eq_append]

/-- Pushing `f 0, …, f (n − 1)` onto the empty array gives their array. -/
theorem foldl_push_eq_ofFn (f : ℕ → UInt8) : ∀ n,
    (List.range n).foldl (fun x j => x.push (f j)) ByteArray.empty =
      ⟨Array.ofFn (n := n) fun j => f j.val⟩
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      foldl_push_eq_ofFn f n, Array.ofFn_succ]
    rfl

/-- One byte `n mod 256`, as EthLib's `i2osp n 1` writes it. -/
theorem uint8_ofNat_and (n : ℕ) : UInt8.ofNat (n &&& 255) = n.toUInt8 := by
  apply UInt8.toNat_inj.mp
  simp only [UInt8.toNat_ofNat', Nat.toUInt8, show (255 : ℕ) = 2 ^ 8 - 1 by rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]

namespace Xmd

/-- `a ⊕ b` on 32 bytes, a missing byte read as zero. -/
def xor32 (a b : ByteArray) : ByteArray :=
  ⟨Array.ofFn (n := 32) fun j => (a[j.val]?.getD 0) ^^^ (b[j.val]?.getD 0)⟩

/-- EthLib's `strxor a b`, over `a`'s bytes (`n` of them), is `xor32` when `n = 32`. -/
theorem strxor_eq {n : ℕ} (a b : ByteArray) (hn : n = 32) :
    (⟨Array.ofFn (n := n) fun i => (a[i.val]?.getD 0) ^^^ (b[i.val]?.getD 0)⟩ : ByteArray) =
      xor32 a b := by
  subst hn; rfl

/-- `expand_message_xmd`'s blocks after `b₀`, `blk k = b_{k+1}`: `b₁` given,
`b_{k+2} = H((b₀ ⊕ b_{k+1}) ‖ I2OSP(k + 2, 1) ‖ DST')`. -/
def blk (b0 dp b1 : ByteArray) : ℕ → ByteArray
  | 0 => b1
  | k + 1 => Ssz.Sha256.hash (xor32 b0 (blk b0 dp b1 k) ++ ⟨#[(k + 2).toUInt8]⟩ ++ dp)

/-- `b₁ ‖ … ‖ b_{k+1}`. -/
def out (b0 dp b1 : ByteArray) : ℕ → ByteArray
  | 0 => b1
  | k + 1 => out b0 dp b1 k ++ blk b0 dp b1 (k + 1)

theorem size_blk {b0 dp b1 : ByteArray} (h1 : b1.size = 32) : ∀ k, (blk b0 dp b1 k).size = 32
  | 0 => h1
  | _ + 1 => Ssz.Sha256.hash_size _

theorem size_out {b0 dp b1 : ByteArray} (h1 : b1.size = 32) : ∀ k, (out b0 dp b1 k).size = 32 * (k + 1)
  | 0 => h1
  | k + 1 => by rw [out, ByteArray.size_append, size_out h1 k, size_blk h1]; ring

/-- The runtime's loop over `i = 2, …, m + 1`, its state `(bᵢ, b₁ ‖ … ‖ bᵢ)`. -/
theorem runtime_loop (b0 dp b1 : ByteArray) (F : ByteArray × ByteArray → ℕ → ByteArray × ByteArray)
    (hF : ∀ s a, F s a = (Ssz.Sha256.hash (xor32 b0 s.1 ++ ⟨#[a.toUInt8]⟩ ++ dp),
      s.2 ++ Ssz.Sha256.hash (xor32 b0 s.1 ++ ⟨#[a.toUInt8]⟩ ++ dp))) :
    ∀ m, (List.range' 2 m).foldl F (b1, b1) = (blk b0 dp b1 m, out b0 dp b1 m)
  | 0 => rfl
  | m + 1 => by
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
      runtime_loop b0 dp b1 F hF m, hF, blk, out, blk, show 2 + 1 * m = m + 2 by ring]

/-- EthLib's loop over `i = 2, …, m + 1`, its state the array `b₁, …, bᵢ`. -/
theorem eth_loop (b0 dp b1 : ByteArray) (G : Array ByteArray → ℕ → Array ByteArray)
    (hG : ∀ bs a, G bs a =
      bs.push (Ssz.Sha256.hash (xor32 b0 (bs[bs.size - 1]?.getD ByteArray.empty) ++
        ⟨#[a.toUInt8]⟩ ++ dp))) :
    ∀ m, ((List.range' 2 m).foldl G #[b1]).toList = (List.range (m + 1)).map (blk b0 dp b1)
  | 0 => rfl
  | m + 1 => by
    have ih := eth_loop b0 dp b1 G hG m
    generalize hbs : (List.range' 2 m).foldl G #[b1] = bs at ih
    have hlast : bs[bs.size - 1]? = some (blk b0 dp b1 m) := by
      rw [← Array.getElem?_toList, ← Array.length_toList, ih]
      simp
    rw [List.range'_concat, List.foldl_append, hbs, List.foldl_cons, List.foldl_nil, hG,
      Array.toList_push, ih, hlast, Option.getD_some, List.range_succ (n := m + 1),
      List.map_append, List.map_singleton, blk, show 2 + 1 * m = m + 2 by ring]

/-- The concatenation of `b₁, …, b_{m+1}` is `out m`. -/
theorem foldl_append_blk (b0 dp b1 : ByteArray) (m : ℕ) :
    ((List.range (m + 1)).map (blk b0 dp b1)).foldl (· ++ ·) ByteArray.empty = out b0 dp b1 m := by
  induction m with
  | zero => simp [out, blk, ByteArray.empty_append]
  | succ m ih => rw [List.range_succ (n := m + 1), List.map_append, List.foldl_append, ih]; rfl

end Xmd

value_eq expandMessageXmd_value : EthLib.Cryptography.Bls.HashToCurve.expandMessageXmd

/-- The runtime's `expandXmd` is EthLib's `expandMessageXmd` asked for 256 bytes, which accepts
that length: `expand_message_xmd(msg, DST, 256)` with SHA-256 (RFC 9380 §5.3.1, §5.3.3). -/
theorem expandXmd_eq (msg dst : ByteArray) :
    EthLib.Cryptography.Bls.HashToCurve.expandMessageXmd msg dst 256 =
      .ok (H2C.expandXmd msg dst) := by
  rw [expandMessageXmd_value]
  delta_private
  unfold H2C.expandXmd
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, Nat.sub_zero, Nat.div_one, bind_pure_comp, map_pure,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv, Nat.reduceMul, Nat.reduceShiftRight,
    gt_iff_lt, Nat.reduceLT, ↓reduceIte, Array.ofFn_succ, Array.ofFn_zero, Fin.val_castSucc,
    Nat.shiftRight_zero, uint8_ofNat_and]
  generalize (if dst.size > 255 then Ssz.Sha256.hash ("H2C-OVERSIZE-DST-".toUTF8 ++ dst) else dst) = d
  have hdp : d ++ ⟨#[].push d.size.toUInt8⟩ = d.push d.size.toUInt8 :=
    (byteArray_push_eq_append d _).symm
  have hzp : H2C.zPad = ⟨Array.replicate 64 0⟩ := by decide +kernel
  have hb0 : (⟨Array.replicate 64 0⟩ : ByteArray) ++ msg ++
      ⟨(#[].push (Nat.toUInt8 1)).push (Nat.toUInt8 256)⟩ ++ ⟨#[].push (Nat.toUInt8 0)⟩ ++
        d.push d.size.toUInt8 =
      H2C.zPad ++ msg ++ ⟨#[1, 0, 0]⟩ ++ d.push d.size.toUInt8 := by
    rw [hzp, ByteArray.append_assoc (a := (⟨Array.replicate 64 0⟩ : ByteArray) ++ msg)]
    rfl
  rw [hdp, hb0]
  have h0 : (Ssz.Sha256.hash (H2C.zPad ++ msg ++ ⟨#[1, 0, 0]⟩ ++ d.push d.size.toUInt8)).size = 32 :=
    Ssz.Sha256.hash_size _
  generalize Ssz.Sha256.hash (H2C.zPad ++ msg ++ ⟨#[1, 0, 0]⟩ ++ d.push d.size.toUInt8) = b0 at h0
  generalize d.push d.size.toUInt8 = dp
  have hb1 : b0 ++ ⟨#[].push (Nat.toUInt8 1)⟩ ++ dp = b0.push 1 ++ dp := by
    rw [byteArray_push_eq_append]; rfl
  rw [hb1]
  have h1 : (Ssz.Sha256.hash (b0.push 1 ++ dp)).size = 32 := Ssz.Sha256.hash_size _
  generalize Ssz.Sha256.hash (b0.push 1 ++ dp) = b1 at h1
  rw [Xmd.runtime_loop b0 dp b1 _ (fun s a => by
    simp only [← List.range_eq_range', foldl_push_eq_ofFn]
    simp only [byteArray_push_eq_append, Xmd.xor32])]
  have hmk : (Array.mkEmpty 8 : Array ByteArray).push b1 = #[b1] := rfl
  rw [hmk, ← Array.foldl_toList, Xmd.eth_loop b0 dp b1 _ (fun bs a => by
    rw [Xmd.strxor_eq _ _ (Ssz.Sha256.hash_size _)]; rfl),
    Xmd.foldl_append_blk,
    show 256 = (Xmd.out b0 dp b1 7).size by rw [Xmd.size_out h1], ByteArray.extract_zero_size]
  rfl

/-- `expand_message_xmd` gives 256 bytes, eight SHA-256 outputs. -/
theorem size_expandXmd (msg dst : ByteArray) : (H2C.expandXmd msg dst).size = 256 := by
  unfold H2C.expandXmd
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, Nat.sub_zero, Nat.div_one, bind_pure_comp, map_pure,
    Nat.reduceSub]
  generalize Ssz.Sha256.hash (H2C.zPad ++ msg ++ ⟨#[1, 0, 0]⟩ ++
    (if dst.size > 255 then Ssz.Sha256.hash ("H2C-OVERSIZE-DST-".toUTF8 ++ dst) else dst).push
      (if dst.size > 255 then Ssz.Sha256.hash ("H2C-OVERSIZE-DST-".toUTF8 ++ dst) else dst).size.toUInt8)
    = b0
  generalize (if dst.size > 255 then Ssz.Sha256.hash ("H2C-OVERSIZE-DST-".toUTF8 ++ dst) else dst).push
      (if dst.size > 255 then Ssz.Sha256.hash ("H2C-OVERSIZE-DST-".toUTF8 ++ dst) else dst).size.toUInt8
    = dp
  have h1 : (Ssz.Sha256.hash (b0.push 1 ++ dp)).size = 32 := Ssz.Sha256.hash_size _
  generalize Ssz.Sha256.hash (b0.push 1 ++ dp) = b1 at h1
  rw [Xmd.runtime_loop b0 dp b1 _ (fun s a => by
    simp only [← List.range_eq_range', foldl_push_eq_ofFn]
    simp only [byteArray_push_eq_append, Xmd.xor32])]
  exact Xmd.size_out h1 7

/-! ## `hash_to_field` -/

/-- EthLib's `Fp2` with the runtime's coordinates. -/
def Fp2.toEth (a : Fp2) : EthLib.Cryptography.Bls.Fp2 :=
  ⟨EthLib.Cryptography.Bls.Fp.ofNat a.c0, EthLib.Cryptography.Bls.Fp.ofNat a.c1⟩

theorem Fp2.ofEth_toEth {a : Fp2} (ha : a.Reduced) : ofEth a.toEth = a := by
  obtain ⟨a0, a1⟩ := a
  obtain ⟨h0, h1⟩ := ha
  simp only [ofEth, Fp2.toEth, EthLib.Cryptography.Bls.Fp.ofNat, Fin.val_ofNat, Fp2.mk.injEq]
  exact ⟨Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1⟩

/-- Byte `i` of the 64 bytes from `s` is byte `s + i`. -/
theorem extract_getD {u : ByteArray} {s i : ℕ} (hi : i < 64) (hs : s + 64 ≤ u.size) :
    (u.extract s (s + 64))[i]?.getD 0 = u[s + i]?.getD 0 := by
  have h1 : i < (u.extract s (s + 64)).size := by rw [ByteArray.size_extract]; omega
  rw [getElem?_pos _ i h1, getElem?_pos u (s + i) (by omega), Option.getD_some, Option.getD_some,
    ByteArray.getElem_extract]

/-- EthLib's `fpFromBytesL` reading of 64 bytes from `s` (shifts and ors) is `beNat`'s. -/
theorem fold_bytes_eq_beNat (u : ByteArray) (s e : ℕ) (he : e = s + 64) (hs : e ≤ u.size) :
    List.foldl (fun b i => b <<< 8 ||| ((u.extract s e)[i]?.getD 0).toNat) 0
      (List.range' 0 (u.extract s e).size) = beNat u s 64 := by
  subst he
  rw [ByteArray.size_extract, show min (s + 64) u.size - s = 64 by omega, ← List.range_eq_range',
    beNat_eq_foldl]
  apply List.foldl_ext
  intro b i hi
  rw [List.mem_range] at hi
  rw [extract_getD hi hs, ← Nat.shiftLeft_add_eq_or_of_lt (UInt8.toNat_lt _), Nat.shiftLeft_eq]

value_eq hashToFieldFp2_value : EthLib.Cryptography.Bls.HashToCurve.hashToFieldFp2

/-- The runtime's `hash_to_field` is EthLib's `hashToFieldFp2 msg dst 2` (RFC 9380 §5.2, `L = 64`),
its two elements read as EthLib's (which never errs here). -/
theorem hashToField_eq (msg dst : ByteArray) :
    EthLib.Cryptography.Bls.HashToCurve.hashToFieldFp2 msg dst 2 =
      .ok #[(H2C.hashToField msg dst).1.toEth, (H2C.hashToField msg dst).2.toEth] := by
  rw [hashToFieldFp2_value]
  delta_private
  have hs := size_expandXmd msg dst
  simp only [Nat.reduceMul, expandXmd_eq, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, List.forIn_pure_yield_eq_foldl, Nat.sub_zero, Nat.div_one,
    Nat.add_sub_cancel, Id.run, bind_pure]
  show Except.ok _ = _
  simp only [List.range'_succ, List.range'_zero, List.foldl_cons, List.foldl_nil, Nat.zero_add,
    Nat.reduceMul, Nat.reduceAdd]
  rw [fold_bytes_eq_beNat _ 0 64 rfl (by omega), fold_bytes_eq_beNat _ 64 128 rfl (by omega),
    fold_bytes_eq_beNat _ 128 192 rfl (by omega), fold_bytes_eq_beNat _ 192 256 rfl (by omega)]
  have hm : ∀ n, EthLib.Cryptography.Bls.Fp.ofNat (n % P) = EthLib.Cryptography.Bls.Fp.ofNat n :=
    fun n => Fin.ext (by
      simp [EthLib.Cryptography.Bls.Fp.ofNat, Fin.ofNat, modulus_eq])
  simp only [H2C.hashToField, Fp2.toEth, hm, Nat.mul_zero, Nat.mul_one, Nat.reduceMul]
  rfl

/-! ## EthLib's square root in `Fp2` -/

value_eq ethFp2Sqrt_value : EthLib.Cryptography.Bls.Fp2.sqrt

set_option linter.auxLemma false in
theorem ethFp2Sqrt_match_1 {β : Type}
    (x : Except EthLib.Cryptography.Bls.BlsError EthLib.Cryptography.Bls.Fp)
    (f : EthLib.Cryptography.Bls.Fp → β) (g : β) :
    EthLib.Cryptography.Bls.Fp2.sqrt.match_1 (fun _ => β) x f (fun _ => g) = x.toOption.elim g f := by
  cases x <;> rfl

set_option linter.auxLemma false in
theorem ethFp2Sqrt_match_3 {β : Type}
    (x : Except EthLib.Cryptography.Bls.BlsError EthLib.Cryptography.Bls.Fp) (g : β)
    (f : EthLib.Cryptography.Bls.Fp → β) :
    EthLib.Cryptography.Bls.Fp2.sqrt.match_3 (fun _ => β) x (fun _ => g) f = x.toOption.elim g f := by
  cases x <;> rfl

theorem toOption_elim {ε α β : Type} (o : Option α) (b : Except ε β) (f : α → Except ε β) :
    (o.elim b f).toOption = o.elim b.toOption fun x => (f x).toOption := by cases o <;> rfl

theorem toOption_elim_self {ε α : Type} (e b : Except ε α) :
    (e.toOption.elim b fun _ => e).toOption = e.toOption.elim b.toOption some := by
  cases e <;> rfl

open EthLib.Cryptography.Bls (Fp) in
/-- The runtime's square root in `Fp2` is EthLib's `Fp2.sqrt`, on EthLib's values: the same root,
and `none` exactly when EthLib errs. (So EthLib's `Fp2.sqrt` returns only roots and finds one
exactly on the squares, by `Fp2.sqrt?_some` and `Fp2.sqrt?_isSome_iff`.) -/
theorem sqrt?_ofEth (a : EthLib.Cryptography.Bls.Fp2) :
    (ofEth a).sqrt? = (EthLib.Cryptography.Bls.Fp2.sqrt a).toOption.map ofEth := by
  rw [Fp2.sqrt?_eq, ethFp2Sqrt_value]
  -- The matches first, then the `have`s: zeta-reducing inside a match's alternatives would have
  -- the kernel unfold the match and evaluate its discriminant.
  simp (config := { iota := false, zeta := false, beta := true, proj := false, decide := false })
    only [ethFp2Sqrt_match_1, ethFp2Sqrt_match_3]
  simp (config := { iota := false, zeta := true, beta := true, proj := false, decide := false })
    only []
  have hc0 : (ofEth a).c0 = a.c0.val := rfl
  have hc1 : (ofEth a).c1 = a.c1.val := rfl
  by_cases hz : a.c1.val = 0
  · rw [ite_eq_left (show (ofEth a).c1 = 0 from hz),
      ite_eq_left (show a.c1.isZero = true by simp [Fp.isZero, hz]), hc0, fsqrt?_val, fneg_val,
      fsqrt?_val]
    cases (Fp.sqrt a.c0).toOption <;> cases (Fp.sqrt (-a.c0)).toOption <;> rfl
  rw [ite_eq_right (show ¬(ofEth a).c1 = 0 from hz),
    ite_eq_right (show ¬a.c1.isZero = true by simp [Fp.isZero, hz]), hc0, hc1]
  have hn : (a.c0.val * a.c0.val + a.c1.val * a.c1.val) % P = (a.c0 * a.c0 + a.c1 * a.c1).val := by
    rw [← cast_inj (Nat.mod_lt _ (by decide)) (val_lt _), ZMod.natCast_mod]; simp
  have hgs : fsqrt? (a.c0 * a.c0 + a.c1 * a.c1).val =
      (Fp.sqrt (a.c0 * a.c0 + a.c1 * a.c1)).toOption.map Fin.val := fsqrt?_val _
  rw [hn, hgs, toOption_elim]
  generalize hg : (Fp.sqrt (a.c0 * a.c0 + a.c1 * a.c1)).toOption = og at hgs
  cases og with
  | none => rfl
  | some g =>
    -- `rw`, not `simp only`: simp's rewriting here had the kernel reduce the matches.
    rw [Option.map_some, Option.elim_some, Option.elim_some]
    beta_reduce
    have hhalf : ((Fp.ofNat 2).inverse.val : GFp) = 2⁻¹ := by
      rw [← finv_val, cast_finv]; simp
    have hA : fadd a.c0.val g.val * ((P + 1) / 2) % P = ((a.c0 + g) * (Fp.ofNat 2).inverse).val := by
      rw [← cast_inj (Nat.mod_lt _ (by decide)) (val_lt _), ZMod.natCast_mod, Nat.cast_mul, cast_fadd,
        cast_half, cast_val_mul, cast_val_add, hhalf]
    have hB : fsub a.c0.val g.val * ((P + 1) / 2) % P = ((a.c0 - g) * (Fp.ofNat 2).inverse).val := by
      rw [← cast_inj (Nat.mod_lt _ (by decide)) (val_lt _), ZMod.natCast_mod, Nat.cast_mul,
        cast_fsub _ (val_lt g).le, cast_half, cast_val_mul, cast_val_sub, hhalf]
    rw [hA, hB, fsqrt?_val, fsqrt?_val, toOption_elim, toOption_elim_self]
    have hgg : (g.val : GFp) * g.val = a.c0.val * a.c0.val + a.c1.val * a.c1.val := by
      have := (fsqrt?_some hgs).2
      rw [← hn, ZMod.natCast_mod] at this; push_cast at this; exact this
    have ha1 : ((a.c1.val : ℕ) : GFp) ≠ 0 := by rwa [Ne, cast_eq_zero (val_lt _)]
    have hy : ∀ x : Fp, ((ofEth a).c1 * finv (fdbl x.val) % P) =
        (a.c1 * (Fp.ofNat 2 * x).inverse).val := by
      intro x
      rw [hc1, ← cast_inj (Nat.mod_lt _ (by decide)) (val_lt _), ZMod.natCast_mod, Nat.cast_mul,
        cast_finv, cast_fdbl, cast_val_mul, ← finv_val, cast_finv, cast_val_mul, cast_val_ofNat]
      push_cast; ring
    have hok : ∀ (x : Fp) (X : Fp), (Fp.sqrt X).toOption = some x →
        (X.val : GFp) = (a.c0.val + g.val) * 2⁻¹ ∨ (X.val : GFp) = (a.c0.val - g.val) * 2⁻¹ →
        (if (Fp2.sqr ⟨x.val, (ofEth a).c1 * finv (fdbl x.val) % P⟩).eq (ofEth a) = true then
          some (⟨x.val, (ofEth a).c1 * finv (fdbl x.val) % P⟩ : Fp2) else none) =
          some (ofEth ⟨x, a.c1 * (Fp.ofNat 2 * x).inverse⟩) := by
      intro x X hx hX
      have hxs : fsqrt? X.val = some x.val := by rw [fsqrt?_val, hx]; rfl
      obtain ⟨-, hsq⟩ := fsqrt?_some hxs
      have h2 := two_ne_zero_GFp
      rw [ite_eq_left (Fp2.sqrt?_check (Fp2.reduced_ofEth a) ha1 hgg (val_lt x) (by
        rw [hc0]
        rcases hX with h | h
        · left; rw [hsq, h]; field_simp
        · right; rw [hsq, h]; field_simp))]
      rw [hy x]; rfl
    generalize h3 : (Fp.sqrt ((a.c0 + g) * (Fp.ofNat 2).inverse)).toOption = o3
    generalize h4 : (Fp.sqrt ((a.c0 - g) * (Fp.ofNat 2).inverse)).toOption = o4
    cases o3 with
    | some x =>
      rw [Option.map_some, Option.elim_some, Option.elim_some, Option.elim_some, Option.elim_some]
      exact hok x _ h3 (Or.inl (by rw [cast_val_mul, cast_val_add, hhalf]))
    | none =>
      cases o4 with
      | none => rfl
      | some x =>
        rw [Option.map_none, Option.elim_none, Option.elim_none, Option.map_some, Option.elim_some,
          Option.elim_some]
        exact hok x _ h4 (Or.inr (by rw [cast_val_mul, cast_val_sub, hhalf]))

/-! ## SSWU -/

section Sswu

open EthLib.Cryptography.Bls.HashToCurve (Z Aprime Bprime)

theorem isZero_ofEth (d : EthLib.Cryptography.Bls.Fp2) : (ofEth d).isZero = d.isZero := by
  have e : ∀ n : ℕ, decide (n = 0) = (n == 0) := fun n => by cases n <;> rfl
  show (decide ((ofEth d).c0 = 0) && decide ((ofEth d).c1 = 0)) = _
  rw [e, e]; rfl

theorem div_ofEth (a b : EthLib.Cryptography.Bls.Fp2) : (ofEth a).mul (ofEth b).inv = ofEth (a / b) := by
  rw [Fp2.inv_ofEth, Fp2.mul_ofEth]; rfl

theorem one_ofEth : Fp2.one = ofEth EthLib.Cryptography.Bls.Fp2.one := rfl

/-- SSWU's `x₁` on EthLib's values is EthLib's. -/
theorem sswuX1_ofEth (u : EthLib.Cryptography.Bls.Fp2) :
    sswuX1 (ofEth u) = ofEth (if (Z * (u * u) * (Z * (u * u)) + Z * (u * u)).isZero = true then
      Bprime / (Z * Aprime)
    else -Bprime / Aprime * (EthLib.Cryptography.Bls.Fp2.one + (Z * (u * u) * (Z * (u * u)) +
      Z * (u * u)).inverse)) := by
  obtain ⟨hA, hB, hZ⟩ := Provenance.sswu_eq
  unfold sswuX1
  rw [hA, hB, hZ, Fp2.sqr_ofEth, Fp2.mul_ofEth, Fp2.sqr_ofEth, Fp2.add_ofEth, isZero_ofEth]
  by_cases h : (Z * (u * u) * (Z * (u * u)) + Z * (u * u)).isZero = true
  · rw [ite_eq_left h, ite_eq_left h, Fp2.mul_ofEth, div_ofEth]
  · rw [ite_eq_right h, ite_eq_right h, Fp2.neg_ofEth, div_ofEth, Fp2.inv_ofEth, one_ofEth,
      Fp2.add_ofEth, Fp2.mul_ofEth]

/-- `g(x)` on EthLib's values is EthLib's `x³ + A'x + B'`. -/
theorem gIso_ofEth (x : EthLib.Cryptography.Bls.Fp2) :
    H2C.gIso (ofEth x) = ofEth (x * x * x + Aprime * x + Bprime) := by
  obtain ⟨hA, hB, -⟩ := Provenance.sswu_eq
  rw [← Fp2.toGF_inj reduced_gIso (Fp2.reduced_ofEth _), toGF_gIso (Fp2.reduced_ofEth x), hA, hB]
  simp only [Fp2.toGF_ofEth_add, Fp2.toGF_ofEth_mul]
  ring

/-- Euler's criterion in `Fp2` on EthLib's values: a square exactly when EthLib's `Fp2.sqrt`
succeeds. -/
theorem isSquare_ofEth (g : EthLib.Cryptography.Bls.Fp2) :
    (ofEth g).isSquare = (EthLib.Cryptography.Bls.Fp2.sqrt g).toOption.isSome := by
  rw [Bool.eq_iff_iff, Fp2.isSquare_iff, ← Fp2.sqrt?_isSome_iff (Fp2.reduced_ofEth g), sqrt?_ofEth,
    Option.isSome_map]

/-- `sgn0`'s choice of sign, EthLib's (its private `sgn0Fp2`, unfolded) on EthLib's values. -/
theorem sgnAdj_ofEth (u y : EthLib.Cryptography.Bls.Fp2) :
    ofEth (if (have s0 := (u.c0.val % 2 == 1); have z0 := u.c0.isZero; have s1 := (u.c1.val % 2 == 1);
        s0 || z0 && s1) = (have s0 := (y.c0.val % 2 == 1); have z0 := y.c0.isZero;
        have s1 := (y.c1.val % 2 == 1); s0 || z0 && s1) then y else -y) =
      sgnAdj (ofEth u) (ofEth y) := by
  have e : ∀ v : EthLib.Cryptography.Bls.Fp2, (ofEth v).sgn0 =
      (have s0 := (v.c0.val % 2 == 1); have z0 := v.c0.isZero; have s1 := (v.c1.val % 2 == 1);
        s0 || z0 && s1) := by
    intro v
    simp only [Fp2.sgn0, ofEth, EthLib.Cryptography.Bls.Fp.isZero]
    cases h0 : v.c0.val % 2 == 1 <;> cases h1 : v.c0.val == 0 <;> cases h2 : v.c1.val % 2 == 1 <;>
      simp_all
  unfold sgnAdj
  rw [e u, e y]
  by_cases h : (have s0 := (u.c0.val % 2 == 1); have z0 := u.c0.isZero;
      have s1 := (u.c1.val % 2 == 1); s0 || z0 && s1) = (have s0 := (y.c0.val % 2 == 1);
      have z0 := y.c0.isZero; have s1 := (y.c1.val % 2 == 1); s0 || z0 && s1)
  · rw [ite_eq_left h, ite_eq_left (by rw [h]; exact beq_self_eq_true _)]
  · rw [ite_eq_right h, ite_eq_right (by rw [beq_iff_eq]; exact h), Fp2.neg_ofEth]

end Sswu

value_eq simpleSwu_value : EthLib.Cryptography.Bls.HashToCurve.simpleSwu

set_option linter.auxLemma false in
theorem simpleSwu_match_1 {β : Type}
    (x : Except EthLib.Cryptography.Bls.BlsError EthLib.Cryptography.Bls.Fp2)
    (f : EthLib.Cryptography.Bls.Fp2 → β) (g : β) :
    EthLib.Cryptography.Bls.HashToCurve.simpleSwu.match_1 (fun _ => β) x f (fun _ => g) =
      x.toOption.elim g f := by
  cases x <;> rfl

open EthLib.Cryptography.Bls.HashToCurve (Z Aprime Bprime) in
/-- **SSWU** (RFC 9380 §6.6.2): the runtime's `sswu?` is EthLib's `simpleSwu`, on EthLib's
values: `none` exactly when EthLib's errs (neither `g(x₁)` nor `g(x₂)` has a root), else the
same point. -/
theorem sswu?_ofEth (u : EthLib.Cryptography.Bls.Fp2) :
    H2C.sswu? (ofEth u) = (EthLib.Cryptography.Bls.HashToCurve.simpleSwu u).toOption.map
      fun xy => (⟨ofEth xy.1, ofEth xy.2⟩ : G2A) := by
  rw [sswu?_eq, simpleSwu_value]
  simp (config := { iota := false, zeta := false, beta := true, proj := false, decide := false })
    only [simpleSwu_match_1]
  simp (config := { iota := false, zeta := true, beta := true, proj := false, decide := false })
    only []
  delta_private
  have e1 := sswuX1_ofEth u
  have e2 : sswuX2 (ofEth u) = ofEth (Z * (u * u) * (if (Z * (u * u) * (Z * (u * u)) +
      Z * (u * u)).isZero = true then Bprime / (Z * Aprime) else -Bprime / Aprime *
      (EthLib.Cryptography.Bls.Fp2.one + (Z * (u * u) * (Z * (u * u)) + Z * (u * u)).inverse))) := by
    obtain ⟨-, -, hZ⟩ := Provenance.sswu_eq
    rw [sswuX2, e1, hZ, Fp2.sqr_ofEth, Fp2.mul_ofEth, Fp2.mul_ofEth]
  generalize Z * (u * u) = zu2 at e1 e2 ⊢
  generalize (if (zu2 * zu2 + zu2).isZero = true then Bprime / (Z * Aprime) else
    -Bprime / Aprime * (EthLib.Cryptography.Bls.Fp2.one + (zu2 * zu2 + zu2).inverse)) = x1 at e1 e2 ⊢
  rw [e1, e2, gIso_ofEth, gIso_ofEth, isSquare_ofEth, sqrt?_ofEth, sqrt?_ofEth, toOption_elim]
  generalize (EthLib.Cryptography.Bls.Fp2.sqrt (x1 * x1 * x1 + Aprime * x1 + Bprime)).toOption = o1
  generalize (EthLib.Cryptography.Bls.Fp2.sqrt (zu2 * x1 * (zu2 * x1) * (zu2 * x1) + Aprime * (zu2 * x1) +
    Bprime)).toOption = o2
  cases o1 with
  | some y =>
    rw [Option.isSome_some, ite_eq_left rfl, Option.map_some, Option.elim_some, Option.elim_some]
    beta_reduce
    rw [Except.toOption, Option.map_some, sgnAdj_ofEth]
  | none =>
    rw [Option.isSome_none, ite_eq_right Bool.false_ne_true, Option.elim_none, toOption_elim]
    cases o2 with
    | none => rfl
    | some y =>
      rw [Option.map_some, Option.elim_some, Option.elim_some]
      beta_reduce
      rw [Except.toOption, Option.map_some, sgnAdj_ofEth]

/-! ## The 3-isogeny -/

section Iso

open EthLib.Cryptography.Bls.HashToCurve (k10 k11 k12 k13 k20 k21 k30 k31 k32 k33 k40 k41 k42)

theorem eval_isoXNum (x : EthLib.Cryptography.Bls.Fp2) :
    Poly.eval H2C.isoXNum.toList (ofEth x).toGF = (ofEth (k13 * (x * x * x) + k12 * (x * x) +
      k11 * x + k10)).toGF := by
  rw [Provenance.isoXNum_eq]
  simp only [Poly.eval, Fp2.toGF_ofEth_add, Fp2.toGF_ofEth_mul]
  ring

theorem eval_isoXDen (x : EthLib.Cryptography.Bls.Fp2) :
    Poly.eval H2C.isoXDen.toList (ofEth x).toGF = (ofEth (x * x + k21 * x + k20)).toGF := by
  rw [Provenance.isoXDen_eq]
  have h1 : (⟨1, 0⟩ : Fp2).toGF = 1 := Fp2.toGF_one
  have h0 : (⟨0, 0⟩ : Fp2).toGF = 0 := Fp2.toGF_zero
  simp only [Poly.eval, Fp2.toGF_ofEth_add, Fp2.toGF_ofEth_mul, h1, h0]
  ring

theorem eval_isoYNum (x : EthLib.Cryptography.Bls.Fp2) :
    Poly.eval H2C.isoYNum.toList (ofEth x).toGF = (ofEth (k33 * (x * x * x) + k32 * (x * x) +
      k31 * x + k30)).toGF := by
  rw [Provenance.isoYNum_eq]
  simp only [Poly.eval, Fp2.toGF_ofEth_add, Fp2.toGF_ofEth_mul]
  ring

theorem eval_isoYDen (x : EthLib.Cryptography.Bls.Fp2) :
    Poly.eval H2C.isoYDen.toList (ofEth x).toGF = (ofEth (x * x * x + k42 * (x * x) + k41 * x +
      k40)).toGF := by
  rw [Provenance.isoYDen_eq]
  have h1 : (⟨1, 0⟩ : Fp2).toGF = 1 := Fp2.toGF_one
  simp only [Poly.eval, Fp2.toGF_ofEth_add, Fp2.toGF_ofEth_mul, h1]
  ring

/-- The runtime's isogeny triple is EthLib's point scaled by `x_den·y_den`: they stand for the
same point, the identity when a denominator vanishes (EthLib's `G2.zero`, the runtime's
`Z = 0`). -/
theorem isoMap_triple (x y : EthLib.Cryptography.Bls.Fp2) :
    (Eth.g2J (EthLib.Cryptography.Bls.HashToCurve.isoMapG2 x y) = Jac.inf ∧
        (H2C.isoMap ⟨ofEth x, ofEth y⟩).toJ 2 = 0) ∨
      ∃ c : GFp2, c ≠ 0 ∧ Eth.g2J (EthLib.Cryptography.Bls.HashToCurve.isoMapG2 x y) 2 = 1 ∧
        (H2C.isoMap ⟨ofEth x, ofEth y⟩).toJ =
          c • Eth.g2J (EthLib.Cryptography.Bls.HashToCurve.isoMapG2 x y) := by
  have hx := Fp2.reduced_ofEth x
  obtain ⟨hxn, exn⟩ := horner_spec _ red_isoXNum hx
  obtain ⟨hxd, exd⟩ := horner_spec _ red_isoXDen hx
  obtain ⟨hyn, eyn⟩ := horner_spec _ red_isoYNum hx
  obtain ⟨hyd, eyd⟩ := horner_spec _ red_isoYDen hx
  rw [eval_isoXNum] at exn
  rw [eval_isoXDen] at exd
  rw [eval_isoYNum] at eyn
  rw [eval_isoYDen] at eyd
  have ht : (H2C.isoMap ⟨ofEth x, ofEth y⟩).toJ =
      ![(ofEth (k13 * (x * x * x) + k12 * (x * x) + k11 * x + k10)).toGF *
          (ofEth (x * x + k21 * x + k20)).toGF * (ofEth (x * x * x + k42 * (x * x) + k41 * x +
            k40)).toGF ^ 2,
        (ofEth y).toGF * (ofEth (k33 * (x * x * x) + k32 * (x * x) + k31 * x + k30)).toGF *
          (ofEth (x * x + k21 * x + k20)).toGF ^ 3 *
          (ofEth (x * x * x + k42 * (x * x) + k41 * x + k40)).toGF ^ 2,
        (ofEth (x * x + k21 * x + k20)).toGF * (ofEth (x * x * x + k42 * (x * x) + k41 * x +
          k40)).toGF] := by
    have hy := Fp2.reduced_ofEth y
    funext i
    fin_cases i <;> simp only [H2C.isoMap, G2J.toJ] <;> fp2_push <;>
      simp only [exn, exd, eyn, eyd, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons] <;> ring
  unfold EthLib.Cryptography.Bls.HashToCurve.isoMapG2
  simp only []
  by_cases hz : ((x * x + k21 * x + k20).isZero || (x * x * x + k42 * (x * x) + k41 * x +
      k40).isZero) = true
  · left
    rw [ite_eq_left hz, Eth.G2.zero_eq]
    refine ⟨rfl, ?_⟩
    rw [ht]
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [Bool.or_eq_true] at hz
    rcases hz with h | h
    · rw [(Eth.fp2_isZero_iff _).mp h, zero_mul]
    · rw [(Eth.fp2_isZero_iff _).mp h, mul_zero]
  · right
    rw [ite_eq_right hz]
    rw [Bool.or_eq_true, not_or] at hz
    have hd1 : (ofEth (x * x + k21 * x + k20)).toGF ≠ 0 := fun e => hz.1 ((Eth.fp2_isZero_iff _).mpr e)
    have hd2 : (ofEth (x * x * x + k42 * (x * x) + k41 * x + k40)).toGF ≠ 0 :=
      fun e => hz.2 ((Eth.fp2_isZero_iff _).mpr e)
    refine ⟨(ofEth (x * x + k21 * x + k20)).toGF * (ofEth (x * x * x + k42 * (x * x) + k41 * x +
      k40)).toGF, mul_ne_zero hd1 hd2, Eth.toGF_ofEth_one, ?_⟩
    have hdiv : ∀ a b : EthLib.Cryptography.Bls.Fp2,
        (ofEth (a / b)).toGF = (ofEth a).toGF * (ofEth b).toGF⁻¹ := fun a b => by
      rw [show a / b = a * b.inverse from rfl, Fp2.toGF_ofEth_mul, Fp2.toGF_ofEth_inverse]
    rw [ht, smul_fin3]
    simp only [Eth.g2J, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, hdiv, Fp2.toGF_ofEth_mul, Eth.toGF_ofEth_one]
    generalize (ofEth (x * x + k21 * x + k20)).toGF = xd at hd1 ⊢
    generalize (ofEth (x * x * x + k42 * (x * x) + k41 * x + k40)).toGF = yd at hd2 ⊢
    funext i
    fin_cases i <;> simp <;> field_simp

/-- From a point of `E''`, the isogeny: the runtime's triple is a point of `E'` (or `Z = 0`),
EthLib's is nonsingular, and they stand for the same point. -/
theorem iso_spec {x y : EthLib.Cryptography.Bls.Fp2} (h : OnIso ⟨ofEth x, ofEth y⟩) :
    (H2C.isoMap ⟨ofEth x, ofEth y⟩).Good ∧
      E2.Nonsingular (Eth.g2J (EthLib.Cryptography.Bls.HashToCurve.isoMapG2 x y)) ∧
      aff2 (H2C.isoMap ⟨ofEth x, ofEth y⟩).toJ =
        aff2 (Eth.g2J (EthLib.Cryptography.Bls.HashToCurve.isoMapG2 x y)) := by
  have hg := isoMap_good ⟨Fp2.reduced_ofEth x, Fp2.reduced_ofEth y⟩ h
  refine ⟨hg, ?_⟩
  rcases isoMap_triple x y with ⟨he, hz⟩ | ⟨c, hc, he⟩
  · rw [he, Point.toAffine_of_Z_eq_zero hz, (Jac.inf_spec _).2]
    exact ⟨(Jac.inf_spec _).1, rfl⟩
  · have hu : IsUnit c := hc.isUnit
    have hz : (H2C.isoMap ⟨ofEth x, ofEth y⟩).toJ 2 ≠ 0 := by
      rw [he.2, smul_fin3]; simp [he.1, hc]
    have hn := hg.2.resolve_left hz
    rw [he.2] at hn ⊢
    exact ⟨(nonsingular_smul _ hu).mp hn, Point.toAffine_smul _ hu⟩

end Iso

/-! ## `hash_to_G2` -/

/-- EthLib's G2 point as the runtime's affine point: `none` for the identity, else EthLib's
`toAffine` coordinates. -/
def Eth.g2Affine? (p : EthLib.Cryptography.Bls.G2) : Option G2A :=
  if p.isInfinity then none else some ⟨ofEth p.toAffine.1, ofEth p.toAffine.2⟩

/-- Two reduced affine points of `E'` standing for the same point are equal. -/
theorem G2A.eq_of_aff {a b : G2A} (ha : a.Reduced) (hb : b.Reduced) (han : E2.Nonsingular a.toJ)
    (hbn : E2.Nonsingular b.toJ) (h : aff2 a.toJ = aff2 b.toJ) : a = b := by
  obtain ⟨ax, ay⟩ := a
  obtain ⟨bx, by'⟩ := b
  simp only [G2A.toJ] at han hbn h
  rw [Point.toAffine_some han, Point.toAffine_some hbn, Affine.Point.some.injEq] at h
  rw [Fp2.toGF_inj ha.1 hb.1, Fp2.toGF_inj ha.2 hb.2] at h
  exact (G2A.mk.injEq _ _ _ _).mpr h

/-- The runtime's `toAffine?` of a reduced nonsingular triple is EthLib's `g2Affine?` of a
nonsingular point standing for the same point. -/
theorem toAffine?_eq_g2Affine? {t : G2J} {e : EthLib.Cryptography.Bls.G2} (ht : t.Reduced)
    (htn : E2.Nonsingular t.toJ) (hen : E2.Nonsingular (Eth.g2J e))
    (h : aff2 t.toJ = aff2 (Eth.g2J e)) : t.toAffine? = Eth.g2Affine? e := by
  have hs := G2J.toAffine?_spec ht htn
  unfold Eth.g2Affine?
  revert hs
  cases t.toAffine? with
  | none =>
    intro hs
    have h0 : aff2 (Eth.g2J e) = 0 := by rw [← h]; exact Point.toAffine_of_Z_eq_zero hs
    rw [ite_eq_left ((Eth.G2.isInfinity_iff_zero hen).mpr h0)]
  | some a =>
    intro hs
    obtain ⟨har, han, hae⟩ := hs
    have hne : aff2 (Eth.g2J e) ≠ 0 := by
      rw [← h, ← hae, G2A.toJ, Point.toAffine_some (by rw [← G2A.toJ]; exact han)]
      exact Affine.Point.some_ne_zero _
    have hi : e.isInfinity = false := by
      cases hc : e.isInfinity
      · rfl
      · exact absurd ((Eth.G2.isInfinity_iff_zero hen).mp hc) hne
    rw [ite_eq_right (by rw [hi]; exact Bool.false_ne_true)]
    obtain ⟨hbn, hbe⟩ := Eth.G2.affine_spec hen hi
    congr 1
    exact G2A.eq_of_aff har ⟨Fp2.reduced_ofEth _, Fp2.reduced_ofEth _⟩ han hbn (by rw [hae, h, ← hbe]; rfl)

/-- `clear_cofactor` of the two isogeny images, both layers: on points of `E''`, the runtime's
`[h_eff](iso(q₀) + iso(q₁))` read as an affine point is EthLib's. -/
theorem hashSum_eq_eth {x0 y0 x1 y1 : EthLib.Cryptography.Bls.Fp2}
    (h0 : OnIso ⟨ofEth x0, ofEth y0⟩) (h1 : OnIso ⟨ofEth x1, ofEth y1⟩) :
    (H2C.clearCofactor ((H2C.isoMap ⟨ofEth x0, ofEth y0⟩).add
        (H2C.isoMap ⟨ofEth x1, ofEth y1⟩))).toAffine? =
      Eth.g2Affine? (EthLib.Cryptography.Bls.HashToCurve.clearCofactor
        ((EthLib.Cryptography.Bls.HashToCurve.isoMapG2 x0 y0).add
          (EthLib.Cryptography.Bls.HashToCurve.isoMapG2 x1 y1))) := by
  obtain ⟨-, hn0, ha0⟩ := iso_spec h0
  obtain ⟨-, hn1, ha1⟩ := iso_spec h1
  obtain ⟨hr, hn, ha⟩ := hashSum_spec (q0 := ⟨ofEth x0, ofEth y0⟩) (q1 := ⟨ofEth x1, ofEth y1⟩)
    ⟨⟨Fp2.reduced_ofEth _, Fp2.reduced_ofEth _⟩, h0⟩ ⟨⟨Fp2.reduced_ofEth _, Fp2.reduced_ofEth _⟩, h1⟩
  obtain ⟨hsn, hsa⟩ := Eth.G2.add_spec hn0 hn1
  unfold EthLib.Cryptography.Bls.HashToCurve.clearCofactor
  obtain ⟨hcn, hca⟩ := Eth.G2.mulNat_spec EthLib.Cryptography.Bls.HashToCurve.hEff hsn
  apply toAffine?_eq_g2Affine? hr hn hcn
  rw [ha, hca, hsa, ← ha0, ← ha1, Provenance.hEff_eq]

value_eq hashToG2_value : EthLib.Cryptography.Bls.HashToCurve.hashToG2

theorem except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

theorem except_bind_error {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl

theorem toOption_ok {ε α : Type} (a : α) : (Except.ok a : Except ε α).toOption = some a := rfl

theorem toOption_error {ε α : Type} (e : ε) : (Except.error e : Except ε α).toOption = none := rfl

/-- **`hash_to_G2` is EthLib's** (RFC 9380's `hash_to_curve` for `BLS12381G2_XMD:SHA-256_SSWU_RO_`,
under any DST): on every message, the runtime's `hashToG2?` is EthLib's `hashToG2` read as an
affine point, `none` exactly when EthLib's errs (SSWU found no root) or returns the identity
(where EthLib returns it, the runtime refuses). Both hash with `Ssz.Sha256.hash`. -/
theorem hashToG2?_eq_eth (msg dst : ByteArray) :
    H2C.hashToG2? msg dst =
      (EthLib.Cryptography.Bls.HashToCurve.hashToG2 msg dst).toOption.bind Eth.g2Affine? := by
  rw [hashToG2?_eq, hashToG2_value]
  beta_reduce
  rw [hashToField_eq, except_bind_ok]
  have hr := reduced_hashToField msg dst
  generalize H2C.hashToField msg dst = uu at hr ⊢
  obtain ⟨u0, u1⟩ := uu
  obtain ⟨hr0, hr1⟩ := hr
  have g0 : (#[u0.toEth, u1.toEth] : Array EthLib.Cryptography.Bls.Fp2)[0]?.getD
      EthLib.Cryptography.Bls.Fp2.zero = u0.toEth := rfl
  have g1 : (#[u0.toEth, u1.toEth] : Array EthLib.Cryptography.Bls.Fp2)[1]?.getD
      EthLib.Cryptography.Bls.Fp2.zero = u1.toEth := rfl
  have hs0 : H2C.sswu? u0 = (EthLib.Cryptography.Bls.HashToCurve.simpleSwu u0.toEth).toOption.map
      fun xy => (⟨ofEth xy.1, ofEth xy.2⟩ : G2A) := by
    rw [← sswu?_ofEth, Fp2.ofEth_toEth hr0]
  have hs1 : H2C.sswu? u1 = (EthLib.Cryptography.Bls.HashToCurve.simpleSwu u1.toEth).toOption.map
      fun xy => (⟨ofEth xy.1, ofEth xy.2⟩ : G2A) := by
    rw [← sswu?_ofEth, Fp2.ofEth_toEth hr1]
  have hq0 := fun q => @sswu?_some u0 q
  have hq1 := fun q => @sswu?_some u1 q
  rw [hs0] at hq0
  rw [hs1] at hq1
  simp only [g0, g1]
  rw [hs0, hs1]
  generalize EthLib.Cryptography.Bls.HashToCurve.simpleSwu u0.toEth = r0 at hq0 ⊢
  generalize EthLib.Cryptography.Bls.HashToCurve.simpleSwu u1.toEth = r1 at hq1 ⊢
  cases r0 with
  | error e => rw [toOption_error, Option.map_none, Option.elim_none, except_bind_error,
      toOption_error, Option.bind_none]
  | ok xy0 =>
    obtain ⟨x0, y0⟩ := xy0
    rw [toOption_ok, Option.map_some, Option.elim_some, except_bind_ok]
    beta_reduce
    cases r1 with
    | error e =>
      rw [toOption_error, Option.map_none, Option.elim_none]
      conv_rhs => dsimp only
      rw [except_bind_error, toOption_error, Option.bind_none]
    | ok xy1 =>
      obtain ⟨x1, y1⟩ := xy1
      rw [toOption_ok, Option.map_some, Option.elim_some]
      beta_reduce
      conv_rhs => dsimp only
      rw [except_bind_ok]
      conv_rhs => dsimp only
      rw [show ∀ c : EthLib.Cryptography.Bls.G2,
        (pure c : Except EthLib.Cryptography.Bls.BlsError EthLib.Cryptography.Bls.G2) = .ok c
          from fun _ => rfl, toOption_ok, Option.bind_some]
      exact hashSum_eq_eth (hq0 ⟨ofEth x0, ofEth y0⟩ rfl).2 (hq1 ⟨ofEth x1, ofEth y1⟩ rfl).2

end LeanLight.Lc.Bls
