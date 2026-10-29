import LeanLight.Ssz.Frame

/-!
# Forks per chain

What the light client knows about each chain it follows, as data (leanKohakuDesktop's `spec/16-light-client.md`,
"Forks per chain"), pinned from each network's `config.yaml` (eth-clients mainnet `8cad480`,
sepolia `7b1b9d9`): the genesis validators root and genesis time, each fork from Electra on with
its epoch and version, the blob-parameter schedule (EIP-7892's BPO entries, which change the
fork digest and not the version), the slot-duration schedule in milliseconds (EIP-8198's
`SLOT_DURATION_SCHEDULE` form), the preset and `MAX_AGE`. `byChainId` finds a chain by its
chain id: mainnet (1) and Sepolia (11155111); the development chain (anvil's 31337) has none,
and `LeanLightProofs.Forks` proves the ids are `Spec.Networks`' (reuse D17). The minimal preset
and the development table the tests use are `LeanLightDev`'s, never linked into a release.

The protocol's arithmetic on slots, all total:

* `epochAt`, `periodAt`: `compute_epoch_at_slot`, `compute_sync_committee_period_at_slot`;
* `forkAt`: the last fork at or before an epoch (`compute_fork_version`'s table walk), `none`
  before the table's first fork, which the light client refuses;
* `signatureVersion`: the fork version a sync aggregate is signed under, the one at the epoch of
  `max(signature_slot, 1) − 1` (`validate_light_client_update`);
* `computeDomain` and `signingRoot`: `compute_domain` and `compute_signing_root`;
* `slotTime` and `slotOf`: `compute_time_at_slot_ms` and `compute_slot_at_time_ms` over the
  chain's slot schedule (consensus-specs master `b834fa8`, `_features/eip8198/beacon-chain.md`),
  in milliseconds since the Unix epoch. A time before genesis is slot 0: Lean's subtraction stops
  at zero where the specification's would fail.
-/

namespace LeanLight.Lc.Forks

open LeanLight.Lc.Ssz (ForkTable Version bytesOf hash64 bytesRoot forkDataRoot)

/-! ## Presets -/

/-- The preset constants the light client reads: `SLOTS_PER_EPOCH`,
`EPOCHS_PER_SYNC_COMMITTEE_PERIOD`, `SYNC_COMMITTEE_SIZE`, and the depth of the committee's key
tree (`floorlog2(SYNC_COMMITTEE_SIZE)`, for its `hash_tree_root`). -/
structure Preset where
  slotsPerEpoch : Nat
  epochsPerPeriod : Nat
  committeeSize : Nat
  committeeDepth : Nat

/-- The mainnet preset: 32 slots an epoch, 256 epochs a period, 512 committee members. -/
def mainnetPreset : Preset := ⟨32, 256, 512, 9⟩

/-! ## Chains -/

/-- The forks whose light-client types the light client decodes: Fulu reuses Electra's. -/
inductive ForkName where
  | electra
  | fulu
  | gloas
  deriving DecidableEq, Repr

/-- One fork of a chain's schedule. -/
structure Fork where
  name : ForkName
  epoch : Nat
  version : Version

/-- What the light client knows about a chain. `forks` are from Electra on, in increasing epoch
order; `blobSchedule` is `BLOB_SCHEDULE`, `(epoch, max blobs)` in increasing epoch order;
`slotSchedule` is `(epoch, slot duration in ms)` in increasing epoch order, its first entry at
epoch 0; `maxAge` is `MAX_AGE` in milliseconds. -/
structure Chain where
  chainId : Nat
  preset : Preset
  genesisValidatorsRoot : ByteArray
  /-- Seconds since the Unix epoch. -/
  genesisTime : Nat
  forks : List Fork
  maxBlobsElectra : Nat
  blobSchedule : List (Nat × Nat)
  slotSchedule : List (Nat × Nat)
  maxAge : Nat

/-- `FAR_FUTURE_EPOCH`. -/
def farFuture : Nat := 2 ^ 64 - 1

/-- `MAX_AGE`: 14 days, in milliseconds (open decision 8). -/
def maxAge14d : Nat := 14 * 24 * 3600 * 1000

namespace Chain

variable (c : Chain)

/-- `compute_epoch_at_slot`. -/
def epochAt (slot : Nat) : Nat := slot / c.preset.slotsPerEpoch

/-- `compute_sync_committee_period_at_slot`. -/
def periodAt (slot : Nat) : Nat := c.epochAt slot / c.preset.epochsPerPeriod

/-- The first slot of `epoch`. -/
def startSlot (epoch : Nat) : Nat := epoch * c.preset.slotsPerEpoch

/-- The last fork at or before `epoch`, if any. -/
def forkAt (epoch : Nat) : Option Fork := (c.forks.filter (·.epoch ≤ epoch)).getLast?

/-- The name of the fork at `epoch`. -/
def forkNameAt (epoch : Nat) : Option ForkName := (c.forkAt epoch).map (·.name)

/-- The version of the fork at `epoch` (`compute_fork_version`). -/
def versionAt (epoch : Nat) : Option Version := (c.forkAt epoch).map (·.version)

/-- The fork the light-client data of a header at `slot` is decoded as. -/
def forkOfSlot (slot : Nat) : Option ForkName := c.forkNameAt (c.epochAt slot)

/-- `GLOAS_FORK_EPOCH`, if scheduled. -/
def gloasEpoch : Option Nat := (c.forks.find? (·.name == .gloas)).map (·.epoch)

/-- Whether a header at `slot` is at or past the Gloas fork: its `execution_block_hash` is the
parent payload's (`Parent`), else its own (`Own`). -/
def gloasAt (slot : Nat) : Bool :=
  match c.gloasEpoch with
  | some e => decide (e ≤ c.epochAt slot)
  | none => false

/-- The epoch of the fork named `n`, `FAR_FUTURE_EPOCH` when not scheduled. -/
def epochOf (n : ForkName) : Nat := ((c.forks.find? (·.name == n)).map (·.epoch)).getD farFuture

/-- The table `compute_fork_digest` reads (`LeanLight.Ssz.ForkTable`). -/
def forkTable : ForkTable :=
  { genesisValidatorsRoot := c.genesisValidatorsRoot,
    forks := c.forks.map fun f => (f.epoch, f.version),
    fuluEpoch := c.epochOf .fulu, electraEpoch := c.epochOf .electra,
    maxBlobsElectra := c.maxBlobsElectra, blobSchedule := c.blobSchedule }

/-- `compute_fork_digest(genesis_validators_root, epoch)`, BPO-aware. -/
def digest (epoch : Nat) : Option ByteArray := c.forkTable.digest epoch

/-! ### Signatures -/

/-- The fork version a sync aggregate signed at `signatureSlot` is checked under: the one at the
epoch of `max(signature_slot, 1) − 1` (`saturating_sub(signature_slot, 1)`). -/
def signatureVersion (signatureSlot : Nat) : Option Version :=
  c.versionAt (c.epochAt (signatureSlot - 1))

/-! ### Time -/

/-- `compute_time_at_slot_ms`: the Unix time in milliseconds at the start of `slot`, walking the
slot schedule from its last entry back, as the specification does. -/
def slotTime (slot : Nat) : Nat :=
  (c.slotSchedule.foldr
    (fun (ed : Nat × Nat) (acc : Nat × Nat) =>
      let forkSlot := c.startSlot ed.1
      if forkSlot < acc.1 then (forkSlot, acc.2 + (acc.1 - forkSlot) * ed.2) else acc)
    (slot, c.genesisTime * 1000)).2

/-- `compute_slot_at_time_ms`: the slot at Unix time `time` (ms), from the last schedule entry
that has begun; slot 0 before genesis. -/
def slotOf (time : Nat) : Nat :=
  let init : Nat × Nat × Nat :=
    (0, c.genesisTime * 1000, ((c.slotSchedule.head?).map (·.2)).getD 0)
  let r := c.slotSchedule.foldl
    (fun (acc : Nat × Nat × Nat) (ed : Nat × Nat) =>
      let forkSlot := c.startSlot ed.1
      let forkTime := c.slotTime forkSlot
      if forkTime ≤ time then (forkSlot, forkTime, ed.2) else acc)
    init
  r.1 + (time - r.2.1) / r.2.2

end Chain

/-! ## Domains -/

/-- `DOMAIN_SYNC_COMMITTEE`. -/
def domainSyncCommittee : ByteArray := bytesOf [0x07, 0, 0, 0]

/-- `compute_domain(domain_type, fork_version, genesis_validators_root)`: the domain type, then
the first 28 bytes of the fork data root. -/
def computeDomain (domainType version gvr : ByteArray) : ByteArray :=
  domainType ++ Bytes.extract (forkDataRoot version gvr) 0 28

/-- `compute_signing_root`: `hash_tree_root(SigningData(object_root, domain))`, two 32-byte
fields. -/
def signingRoot (objectRoot domain : ByteArray) : ByteArray := hash64 objectRoot domain

/-! ## The chain table -/

/-- Mainnet (chain 1): genesis validators root
`0x4b363db94e286120d76eb905340fdd4e54bfe9f06bf33ff6cf5ad27f511bfe95`, genesis time 1606824023;
Electra at 364032 (`0x05000000`), Fulu at 411392 (`0x06000000`); BPO1 at 412672 (15 blobs),
BPO2 at 419072 (21); 12-second slots. No Gloas epoch is scheduled. -/
def mainnet : Chain :=
  { chainId := 1, preset := mainnetPreset,
    genesisValidatorsRoot := bytesOf [0x4b, 0x36, 0x3d, 0xb9, 0x4e, 0x28, 0x61, 0x20, 0xd7, 0x6e,
      0xb9, 0x05, 0x34, 0x0f, 0xdd, 0x4e, 0x54, 0xbf, 0xe9, 0xf0, 0x6b, 0xf3, 0x3f, 0xf6, 0xcf,
      0x5a, 0xd2, 0x7f, 0x51, 0x1b, 0xfe, 0x95],
    genesisTime := 1606824023,
    forks := [⟨.electra, 364032, bytesOf [0x05, 0, 0, 0]⟩, ⟨.fulu, 411392, bytesOf [0x06, 0, 0, 0]⟩],
    maxBlobsElectra := 9, blobSchedule := [(412672, 15), (419072, 21)],
    slotSchedule := [(0, 12000)], maxAge := maxAge14d }

/-- Sepolia (chain 11155111): genesis validators root
`0xd8ea171f3c94aea21ebc42a1ed61052acf3f9209c00e4efbaaddac09ed9b8078`, genesis time 1655733600;
Electra at 222464 (`0x90000074`), Fulu at 272640 (`0x90000075`), Gloas at 353024 (`0x90000076`,
slot 11,296,768, period 1379); BPO1 at 274176 (15 blobs), BPO2 at 275712 (21); 12-second slots. -/
def sepolia : Chain :=
  { chainId := 11155111, preset := mainnetPreset,
    genesisValidatorsRoot := bytesOf [0xd8, 0xea, 0x17, 0x1f, 0x3c, 0x94, 0xae, 0xa2, 0x1e, 0xbc,
      0x42, 0xa1, 0xed, 0x61, 0x05, 0x2a, 0xcf, 0x3f, 0x92, 0x09, 0xc0, 0x0e, 0x4e, 0xfb, 0xaa,
      0xdd, 0xac, 0x09, 0xed, 0x9b, 0x80, 0x78],
    genesisTime := 1655733600,
    forks := [⟨.electra, 222464, bytesOf [0x90, 0, 0, 0x74]⟩,
      ⟨.fulu, 272640, bytesOf [0x90, 0, 0, 0x75]⟩, ⟨.gloas, 353024, bytesOf [0x90, 0, 0, 0x76]⟩],
    maxBlobsElectra := 9, blobSchedule := [(274176, 15), (275712, 21)],
    slotSchedule := [(0, 12000)], maxAge := maxAge14d }

/-- Every chain the light client follows. -/
def chains : List Chain := [mainnet, sepolia]

/-- The chain with chain id `id`, if the light client follows it. -/
def byChainId (id : Nat) : Option Chain := chains.find? (·.chainId == id)

end LeanLight.Lc.Forks
