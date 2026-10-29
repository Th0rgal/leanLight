/-!
# Read decisions specification

Which block to read at is no longer decided here: the light client's anchor, or one endpoint's
word (decided 2026-10-28: no quorum, `spec/04-verified-reads.md`).

**Base fee** (EIP-1559, `calculate_base_fee_per_gas` in the EIP's specification, with
`ELASTICITY_MULTIPLIER = 2` and `BASE_FEE_MAX_CHANGE_DENOMINATOR = 8`, `elasticityMultiplier` and
`baseFeeMaxChangeDenominator`): `nextBaseFee`.
`lkd_verified::reads::next_base_fee` computes in 128 bits and refuses a step that does not fit
(`nextBaseFeeU128`): what it returns is EIP-1559's (`nextBaseFeeU128_sound`), and below a base
fee of 2^64 wei per gas it always returns it (`nextBaseFeeU128_complete`).

**Pending nonce**: `pendingNonce proved last` is `max proved (last + 1)`, the nonce after the
last one `keyd` signed, unless the head has already proved a higher one (`pendingNonce_max`).
-/

namespace LeanLight.Spec.Reads

/-! ## Base fee -/

/-- EIP-1559's `ELASTICITY_MULTIPLIER`: the gas target is the gas limit over it. -/
def elasticityMultiplier : Nat := 2

/-- EIP-1559's `BASE_FEE_MAX_CHANGE_DENOMINATOR`: the base fee moves by at most one over it of
itself per block. -/
def baseFeeMaxChangeDenominator : Nat := 8

/-- EIP-1559's base fee of the block after one with base fee `b`, gas used `used` and gas limit
`limit`; `none` when that block's gas target is zero. -/
def nextBaseFee (b used limit : Nat) : Option Nat :=
  let target := limit / elasticityMultiplier
  if target = 0 then none
  else if used = target then some b
  else if target < used then
    some (b + max (b * (used - target) / target / baseFeeMaxChangeDenominator) 1)
  else some (b - b * (target - used) / target / baseFeeMaxChangeDenominator)

/-- What `lkd_verified::reads::next_base_fee` computes: `nextBaseFee`, refused when a product
or the sum does not fit in 128 bits. -/
def nextBaseFeeU128 (b used limit : Nat) : Option Nat :=
  let target := limit / elasticityMultiplier
  if target = 0 then none
  else if used = target then some b
  else if target < used then
    let delta := max (b * (used - target) / target / baseFeeMaxChangeDenominator) 1
    if (2 ^ 128 - 1) / (used - target) < b then none
    else if 2 ^ 128 - 1 - delta < b then none
    else some (b + delta)
  else
    if (2 ^ 128 - 1) / (target - used) < b then none
    else some (b - b * (target - used) / target / baseFeeMaxChangeDenominator)

/-- What the code returns is EIP-1559's base fee. -/
theorem nextBaseFeeU128_sound {b used limit x : Nat} (h : nextBaseFeeU128 b used limit = some x) :
    nextBaseFee b used limit = some x := by
  unfold nextBaseFeeU128 at h
  unfold nextBaseFee
  dsimp only [elasticityMultiplier, baseFeeMaxChangeDenominator] at h ⊢
  split at h
  · contradiction
  · rename_i h0
    rw [if_neg h0]
    split at h
    · rename_i h1; rw [if_pos h1]; exact h
    · rename_i h1
      rw [if_neg h1]
      split at h
      · rename_i h2
        rw [if_pos h2]
        split at h
        · contradiction
        · split at h
          · contradiction
          · exact h
      · rename_i h2
        rw [if_neg h2]
        split at h
        · contradiction
        · exact h

/-- Below a base fee of 2^64 wei per gas, with 64-bit gas, the code always returns EIP-1559's base
fee. -/
theorem nextBaseFeeU128_complete {b used limit : Nat} (hb : b < 2 ^ 64) (hu : used < 2 ^ 64)
    (hl : limit < 2 ^ 64) : nextBaseFeeU128 b used limit = nextBaseFee b used limit := by
  unfold nextBaseFeeU128 nextBaseFee
  dsimp only [elasticityMultiplier, baseFeeMaxChangeDenominator]
  split
  · rfl
  · rename_i h0
    split
    · rfl
    · rename_i h1
      have hprod : ∀ d, d < 2 ^ 64 → b * d ≤ 2 ^ 128 - 1 := by
        intro d hd
        have : b * d < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hb hd
        omega
      have hdiv : ∀ d, 0 < d → d < 2 ^ 64 → ¬(2 ^ 128 - 1) / d < b := by
        intro d hd0 hd
        rw [Nat.not_lt, Nat.le_div_iff_mul_le hd0]
        exact hprod d hd
      split
      · rename_i h2
        rw [if_neg (hdiv _ (by omega) (by omega))]
        have hinc : max (b * (used - limit / 2) / (limit / 2) / 8) 1 ≤ 2 ^ 64 * 2 ^ 64 / 8 := by
          have : b * (used - limit / 2) / (limit / 2) / 8 ≤ b * (used - limit / 2) / 8 :=
            Nat.div_le_div_right (Nat.div_le_self _ _)
          have := hprod (used - limit / 2) (by omega)
          omega
        rw [if_neg (by omega)]
      · rename_i h2
        rw [if_neg (hdiv _ (by omega) (by omega))]

/-! ## Pending nonce -/

/-- The nonce of the next transaction: `max proved (last + 1)`, or `proved` when nothing was
signed; `none` when `last + 1` is 2^64. -/
def pendingNonce (proved : Nat) (last : Option Nat) : Option Nat :=
  match last with
  | none => some proved
  | some l => if l + 1 < 2 ^ 64 then some (max proved (l + 1)) else none

/-- When `keyd` last signed nonce `l`, the pending nonce is `max proved (l + 1)`: above `l`, and
never below the proved one. -/
theorem pendingNonce_max {proved l n : Nat} (h : pendingNonce proved (some l) = some n) :
    n = max proved (l + 1) ∧ proved ≤ n ∧ l < n := by
  unfold pendingNonce at h
  simp only at h
  split at h
  · cases h
    have := Nat.le_max_right proved (l + 1)
    exact ⟨rfl, Nat.le_max_left _ _, by omega⟩
  · contradiction

end LeanLight.Spec.Reads
