import LeanLight.Forks

/-!
# The chain table (25d, 25i)

About `LeanLight.Forks`, the table the store runs on:

* **Mainnet and Sepolia**: the table follows exactly chain ids 1 and 11155111
  (`byChainId_isSome`); a chain found by an id has that id (`byChainId_chainId`).
* **Distinct chains** (25d): no two chains of the table share a genesis validators root
  (`gvrs_nodup`), so a signature checked under one chain's domain names that chain.
* **The signature's fork version** (25d): the version at the epoch of
  `max(signature_slot, 1) − 1` (`signatureVersion_eq`).
* **Time** (25i): on a chain with one slot duration `d` from genesis, as both tables are
  (`mainnet_schedule`, `sepolia_schedule`), `slotTime` is `genesis + slot·d` in milliseconds
  (`slotTime_single`), `slotOf` is the time since genesis divided by `d`, slot 0 before genesis
  (`slotOf_single`), and the two form a Galois connection (`slotTime_le_iff`): a slot has begun
  by time `t` exactly when it is at most `slotOf t`, for `t` from genesis on. Both are total by
  their types, and their subtractions stop at zero.
* **The presets and `MAX_AGE`** of both chains: the mainnet preset (512 members, 32 slots, 256
  epochs) and 14 days (`mainnet_constants`, `sepolia_constants`).
-/

namespace LeanLight.Lc.Forks

/-! ## The table's chains -/

/-- The chains the light client follows are exactly mainnet (1) and Sepolia (11155111). -/
theorem byChainId_isSome (id : Nat) : (byChainId id).isSome ↔ id = 1 ∨ id = 11155111 := by
  by_cases a : id = 1
  · subst a; exact ⟨fun _ => Or.inl rfl, fun _ => by decide⟩
  by_cases b : id = 11155111
  · subst b; exact ⟨fun _ => Or.inr rfl, fun _ => by decide⟩
  have h1 : mainnet.chainId = 1 := rfl
  have h2 : sepolia.chainId = 11155111 := rfl
  have hn : byChainId id = none := by
    have e1 : (1 == id) = false := by simpa [beq_iff_eq] using Ne.symm a
    have e2 : (11155111 == id) = false := by simpa [beq_iff_eq] using Ne.symm b
    simp only [byChainId, chains, List.find?_cons, List.find?_nil, h1, h2, e1, e2]
  simp [hn, a, b]

/-- A chain found by an id has that id. -/
theorem byChainId_chainId {id : Nat} {c : Chain} (h : byChainId id = some c) : c.chainId = id := by
  unfold byChainId at h
  have := List.find?_some h
  simpa using this

/-- No two chains of the table share a genesis validators root. -/
theorem gvrs_nodup : (chains.map (·.genesisValidatorsRoot)).Nodup := by decide

/-- Nor a chain id. -/
theorem chainIds_nodup : (chains.map (·.chainId)).Nodup := by decide

/-- The genesis validators roots are 32 bytes. -/
theorem gvr_size : ∀ c ∈ chains, c.genesisValidatorsRoot.size = 32 := by decide

/-! ## The signature's fork version -/

/-- A sync aggregate signed at `s` is checked under the version of the fork at the epoch of
`max(s, 1) − 1`. -/
theorem signatureVersion_eq (c : Chain) (s : Nat) :
    c.signatureVersion s = c.versionAt (c.epochAt (max s 1 - 1)) := by
  unfold Chain.signatureVersion
  congr 2
  omega

/-! ## Time -/

/-- `slotTime` on a chain with one slot duration `d` from genesis. -/
theorem slotTime_single (c : Chain) {d : Nat} (h : c.slotSchedule = [(0, d)]) (s : Nat) :
    c.slotTime s = c.genesisTime * 1000 + s * d := by
  unfold Chain.slotTime Chain.startSlot
  rw [h]
  simp only [List.foldr_cons, List.foldr_nil, Nat.zero_mul]
  split
  · simp only [Nat.sub_zero]
  · rename_i hs
    have : s = 0 := by omega
    subst this
    simp

/-- `slotOf` on a chain with one slot duration `d` from genesis: slot 0 before genesis. -/
theorem slotOf_single (c : Chain) {d : Nat} (h : c.slotSchedule = [(0, d)]) (t : Nat) :
    c.slotOf t = (t - c.genesisTime * 1000) / d := by
  unfold Chain.slotOf Chain.startSlot
  rw [h]
  simp only [List.foldl_cons, List.foldl_nil, Nat.zero_mul, List.head?_cons, Option.map_some,
    Option.getD_some]
  rw [slotTime_single c h 0]
  split <;> simp

/-- A slot has begun by time `t` (from genesis on) exactly when it is at most `slotOf t`. -/
theorem slotTime_le_iff (c : Chain) {d : Nat} (h : c.slotSchedule = [(0, d)]) (hd : 0 < d)
    {t : Nat} (ht : c.genesisTime * 1000 ≤ t) (s : Nat) :
    c.slotTime s ≤ t ↔ s ≤ c.slotOf t := by
  rw [slotTime_single c h, slotOf_single c h, Nat.le_div_iff_mul_le hd]
  omega

/-- Both tables have 12-second slots from genesis. -/
theorem mainnet_schedule : mainnet.slotSchedule = [(0, 12000)] := rfl
theorem sepolia_schedule : sepolia.slotSchedule = [(0, 12000)] := rfl

/-- Mainnet's preset and `MAX_AGE`: 512 members, 32 slots an epoch, 256 epochs a period, 14
days. -/
theorem mainnet_constants :
    mainnet.preset.committeeSize = 512 ∧ mainnet.preset.slotsPerEpoch = 32 ∧
      mainnet.preset.epochsPerPeriod = 256 ∧ mainnet.maxAge = 14 * 24 * 3600 * 1000 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Sepolia's: the same. -/
theorem sepolia_constants :
    sepolia.preset.committeeSize = 512 ∧ sepolia.preset.slotsPerEpoch = 32 ∧
      sepolia.preset.epochsPerPeriod = 256 ∧ sepolia.maxAge = 14 * 24 * 3600 * 1000 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Sepolia's Gloas is at epoch 353024; mainnet schedules none. -/
theorem gloas_epochs : sepolia.gloasEpoch = some 353024 ∧ mainnet.gloasEpoch = none := by decide

end LeanLight.Lc.Forks
