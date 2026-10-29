import LeanLight.El.History

/-!
# EIP-2935's history contract, read under a state root (LC8)

About `LeanLight.El.History.blockHash`, the code `lkd-lc` runs:

* `blockHash_spec`: a hash it reads is what `Spec.Mpt` proves the history contract's account
  (holding the EIP's code) and its slot `n mod 8191` hold under the state root, a nonzero value,
  written back as 32 bytes;
* `blockHash_binding`: two proofs that read different hashes for one block under one root hold
  a Keccak-256 collision, in the account's proof or in the slot's.
-/

namespace LeanLight.Lc.History

open LeanLight.Spec.Rlp (be beValue_be be_length_le)
open LeanLight.Spec.Mpt (account storage IsCollision collision)

/-- A storage value is below 2^256. -/
theorem storage_lt {root s p : Bytes} {x : Nat} (h : storage root s p = some x) : x < 2 ^ 256 := by
  unfold storage at h
  split at h
  · cases h
  · cases h; exact Nat.two_pow_pos 256
  · exact ((Spec.Mpt.slotOf_iff _ x).mp h).2.1

/-- A word is 32 bytes. -/
theorem word_length {x : Nat} (h : x < 2 ^ 256) : (word x).length = 32 := by
  have := be_length_le (k := 32) (x := x) (by simpa using h)
  simp only [word, List.length_append, List.length_replicate]
  omega

/-- Words are injective below 2^256: the value is the word's big-endian value. -/
theorem word_injective {x y : Nat} (hx : x < 2 ^ 256) (hy : y < 2 ^ 256) (h : word x = word y) :
    x = y := by
  have hlx := be_length_le (k := 32) (x := x) (by simpa using hx)
  have hly := be_length_le (k := 32) (x := y) (by simpa using hy)
  have hv : ∀ z, Spec.Rlp.beValue (word z) = z := by
    intro z
    simp only [word]
    induction (32 - (be z).length) with
    | zero => simp [beValue_be]
    | succ k ih => rw [List.replicate_succ, List.cons_append, Spec.Rlp.beValue_zero_cons, ih]
  rw [← hv x, ← hv y, h]

/-- **What `blockHash` reads.** The history contract's account, as `Spec.Mpt.account` proves it
under `stateRoot`, holds the contract's code, and its slot for block `n` a nonzero value, as
`Spec.Mpt.storage` proves it under the account's storage root; the hash is that value's word. -/
theorem blockHash_spec {stateRoot : Bytes} {ap sp : ByteArray} {n : Nat} {h : Bytes}
    (hb : blockHash stateRoot ap sp n = some h) :
    ∃ acct x, account stateRoot address ap.data.toList = some acct ∧
      acct.codeHash = Spec.Header.keccak code ∧
      storage acct.storageRoot (slot n) sp.data.toList = some x ∧ x ≠ 0 ∧ x < 2 ^ 256 ∧
      h = word x ∧ h.length = 32 := by
  unfold blockHash at hb
  rw [Spec.Mpt.accountB_eq] at hb
  cases ha : account stateRoot address ap.data.toList with
  | none => rw [ha] at hb; cases hb
  | some acct =>
    rw [ha] at hb
    simp only at hb
    split at hb
    · rename_i hc
      rw [Spec.Mpt.storageB_eq] at hb
      cases hs : storage acct.storageRoot (slot n) sp.data.toList with
      | none => rw [hs] at hb; cases hb
      | some x =>
        rw [hs] at hb
        simp only at hb
        split at hb
        · cases hb
        · rename_i hx
          cases hb
          have hlt := storage_lt hs
          exact ⟨acct, x, rfl, hc, hs, hx, hlt, rfl, word_length hlt⟩
    · cases hb

/-- **Binding.** Two proofs that read different hashes for block `n` under one state root hold
a Keccak-256 collision: in the two account proofs, or in the two slot proofs under the
account's storage root. -/
theorem blockHash_binding {stateRoot : Bytes} {ap₁ sp₁ ap₂ sp₂ : ByteArray} {n : Nat}
    {h₁ h₂ : Bytes} (hb₁ : blockHash stateRoot ap₁ sp₁ n = some h₁)
    (hb₂ : blockHash stateRoot ap₂ sp₂ n = some h₂) (hne : h₁ ≠ h₂) :
    IsCollision (collision stateRoot (Spec.Header.keccak address) ap₁.data.toList
        ap₂.data.toList) ∨
      ∃ sr, IsCollision (collision sr (Spec.Header.keccak (slot n)) sp₁.data.toList
        sp₂.data.toList) := by
  obtain ⟨a₁, x₁, ha₁, -, hs₁, -, hl₁, rfl, -⟩ := blockHash_spec hb₁
  obtain ⟨a₂, x₂, ha₂, -, hs₂, -, hl₂, rfl, -⟩ := blockHash_spec hb₂
  by_cases ha : a₁ = a₂
  · subst ha
    refine .inr ⟨a₁.storageRoot, Spec.Mpt.storage_binding hs₁ hs₂ ?_⟩
    rintro rfl
    exact hne rfl
  · exact .inl (Spec.Mpt.account_binding ha₁ ha₂ ha)

end LeanLight.Lc.History
