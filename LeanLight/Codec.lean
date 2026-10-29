import LeanLight.Store

/-!
# From bytes to the store's objects

The light-client objects arrive as SSZ (`docs/spec-16-light-client.md`, "The beacon API"), each
tagged with its fork: an `Eth-Consensus-Version` name, or a `/updates` chunk's fork digest. A
`Codec` decodes the SSZ of one fork into the store's normalized objects (`LeanLight.Store`); `mainnet`
is the mainnet preset's, from `LeanLight.Ssz`'s decoders (LC3); the minimal preset's, for the tests,
is `LeanLightDev`'s.

**Strict forks** (G8, 25a, 25d). `decode` decodes bytes only as the fork their tag names, and
keeps them only when that is the fork `Forks` gives for the attested slot (the bootstrap's
header slot), and, for a digest, when it is `compute_fork_digest` at that slot's epoch. A tag
the table lacks, or another fork than the slot's, is refused. Nothing is chosen by trying
decoders in turn (helios's trial parse).

A finality or optimistic update enters as a full update with its missing fields empty
(`process_light_client_finality_update`, `process_light_client_optimistic_update`).
-/

namespace LeanLight.Lc.Codec

open LeanLight.Lc.Ssz (BeaconBlockHeader SyncCommittee SyncAggregate ExecutionPayloadHeader zeroChunk)
open LeanLight.Lc.Forks (Chain Preset ForkName)
open LeanLight.Lc.Store (Header Exec Update Bootstrap)

/-- Which light-client object the bytes are. -/
inductive Kind where
  | update
  | finality
  | optimistic
  deriving DecidableEq

/-- Decoders of one preset, by fork. -/
structure Codec where
  bootstrap : ForkName → ByteArray → Option Bootstrap
  update : Kind → ForkName → ByteArray → Option Update

/-- How a source named the fork of its bytes. -/
inductive Tag where
  /-- `Eth-Consensus-Version`, or a re-encoded chunk's fork name. -/
  | name (f : ForkName)
  /-- An SSZ-native `/updates` chunk's fork digest. -/
  | digest (d : ByteArray)

/-! ## Empty fields -/

/-- `n` zero roots. -/
def zeroBranch (n : Nat) : Array ByteArray := Array.replicate n zeroChunk

/-- `SyncCommittee.empty()` of a preset: every key 48 zero bytes. -/
def emptyCommittee (p : Preset) : SyncCommittee :=
  ⟨Array.replicate p.committeeSize ⟨Array.replicate 48 0⟩, ⟨Array.replicate 48 0⟩⟩

/-- The empty beacon block header. -/
def emptyBeacon : BeaconBlockHeader := ⟨0, 0, zeroChunk, zeroChunk, zeroChunk⟩

/-- `ExecutionPayloadHeader.empty()`. -/
def emptyPayload : ExecutionPayloadHeader :=
  { parentHash := zeroChunk, feeRecipient := ⟨Array.replicate 20 0⟩, stateRoot := zeroChunk,
    receiptsRoot := zeroChunk, logsBloom := ⟨Array.replicate 256 0⟩, prevRandao := zeroChunk,
    blockNumber := 0, gasLimit := 0, gasUsed := 0, timestamp := 0, extraData := .empty,
    baseFeePerGas := 0, blockHash := zeroChunk, transactionsRoot := zeroChunk,
    withdrawalsRoot := zeroChunk, blobGasUsed := 0, excessBlobGas := 0 }

/-- An Electra `LightClientHeader.empty()`. -/
def emptyElectra : Header := ⟨emptyBeacon, .payload emptyPayload, zeroBranch 4⟩

/-- A Gloas `LightClientHeader.empty()`. -/
def emptyGloas : Header := ⟨emptyBeacon, .blockHash zeroChunk, zeroBranch 11⟩

/-! ## The mainnet preset, from `LeanLight.Ssz` -/

/-- An Electra or Fulu header. -/
def ofElectra (h : Ssz.Electra.Header) : Header := ⟨h.beacon, .payload h.execution, h.executionBranch⟩

/-- A Gloas header. -/
def ofGloas (h : Ssz.Gloas.Header) : Header := ⟨h.beacon, .blockHash h.executionBlockHash, h.executionBranch⟩

/-- A mainnet-preset bootstrap of fork `f`. -/
def mainnetBootstrap (f : ForkName) (bs : ByteArray) : Option Bootstrap :=
  match f with
  | .electra | .fulu =>
    (Ssz.Electra.Bootstrap.decode bs).map fun b =>
      ⟨ofElectra b.header, b.currentSyncCommittee, b.currentSyncCommitteeBranch⟩
  | .gloas =>
    (Ssz.Gloas.Bootstrap.decode bs).map fun b =>
      ⟨ofGloas b.header, b.currentSyncCommittee, b.currentSyncCommitteeBranch⟩

/-- A mainnet-preset update, finality update or optimistic update of fork `f`. -/
def mainnetUpdate (k : Kind) (f : ForkName) (bs : ByteArray) : Option Update :=
  let p := Forks.mainnetPreset
  match f, k with
  | .gloas, .update =>
    (Ssz.Gloas.Update.decode bs).map fun u =>
      ⟨ofGloas u.attestedHeader, u.nextSyncCommittee, u.nextSyncCommitteeBranch,
        ofGloas u.finalizedHeader, u.finalityBranch, u.syncAggregate, u.signatureSlot⟩
  | .gloas, .finality =>
    (Ssz.Gloas.FinalityUpdate.decode bs).map fun u =>
      ⟨ofGloas u.attestedHeader, emptyCommittee p, zeroBranch Ssz.Gloas.syncCommitteeBranchLength,
        ofGloas u.finalizedHeader, u.finalityBranch, u.syncAggregate, u.signatureSlot⟩
  | .gloas, .optimistic =>
    (Ssz.Gloas.OptimisticUpdate.decode bs).map fun u =>
      ⟨ofGloas u.attestedHeader, emptyCommittee p, zeroBranch Ssz.Gloas.syncCommitteeBranchLength,
        emptyGloas, zeroBranch Ssz.Gloas.finalityBranchLength, u.syncAggregate, u.signatureSlot⟩
  | _, .update =>
    (Ssz.Electra.Update.decode bs).map fun u =>
      ⟨ofElectra u.attestedHeader, u.nextSyncCommittee, u.nextSyncCommitteeBranch,
        ofElectra u.finalizedHeader, u.finalityBranch, u.syncAggregate, u.signatureSlot⟩
  | _, .finality =>
    (Ssz.Electra.FinalityUpdate.decode bs).map fun u =>
      ⟨ofElectra u.attestedHeader, emptyCommittee p,
        zeroBranch Ssz.Electra.syncCommitteeBranchLength, ofElectra u.finalizedHeader,
        u.finalityBranch, u.syncAggregate, u.signatureSlot⟩
  | _, .optimistic =>
    (Ssz.Electra.OptimisticUpdate.decode bs).map fun u =>
      ⟨ofElectra u.attestedHeader, emptyCommittee p,
        zeroBranch Ssz.Electra.syncCommitteeBranchLength, emptyElectra,
        zeroBranch Ssz.Electra.finalityBranchLength, u.syncAggregate, u.signatureSlot⟩

/-- The mainnet preset's codec. -/
def mainnet : Codec := ⟨mainnetBootstrap, mainnetUpdate⟩

/-! ## Tags -/

/-- The fork a digest names in the chain's table: the fork at the first epoch, among the forks'
and the blob schedule's, whose digest it is. -/
def forkOfDigest (c : Chain) (d : ByteArray) : Option ForkName :=
  let epochs := c.forks.map (·.epoch) ++ c.blobSchedule.map (·.1)
  (epochs.find? fun e => c.digest e = some d).bind c.forkNameAt

/-- The fork a tag names, if the table knows it. -/
def tagFork (c : Chain) : Tag → Option ForkName
  | .name f => some f
  | .digest d => forkOfDigest c d

/-- Whether a tag fits a slot: a name always (its fork is compared apart), a digest when it is
the chain's digest at the slot's epoch. -/
def tagFits (c : Chain) (slot : Nat) : Tag → Bool
  | .name _ => true
  | .digest d => decide (c.digest (c.epochAt slot) = some d)

/-- An update of kind `k`, decoded only as the fork its tag names, and kept only when that is the
fork of its attested slot and the tag fits that slot. -/
def decodeUpdate (codec : Codec) (c : Chain) (k : Kind) (tag : Tag) (bs : ByteArray) :
    Option Update :=
  match tagFork c tag with
  | none => none
  | some f =>
    match codec.update k f bs with
    | none => none
    | some u => if c.forkOfSlot u.slot = some f && tagFits c u.slot tag then some u else none

/-- A bootstrap, decoded only as the fork its tag names, and kept only when that is the fork of its
header's slot and the tag fits that slot. -/
def decodeBootstrap (codec : Codec) (c : Chain) (tag : Tag) (bs : ByteArray) : Option Bootstrap :=
  match tagFork c tag with
  | none => none
  | some f =>
    match codec.bootstrap f bs with
    | none => none
    | some b =>
      if c.forkOfSlot b.header.beacon.slot = some f && tagFits c b.header.beacon.slot tag then
        some b
      else none

end LeanLight.Lc.Codec
