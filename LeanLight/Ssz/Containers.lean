import LeanLight.Ssz.Merkle

/-!
# SSZ: the light-client containers

Typed decoders and `hash_tree_root` for exactly the containers the light client reads, as
consensus-specs v1.7.0-beta.4 defines them (`altair`, `capella`, `deneb`, `electra` and `gloas`
`light-client/sync-protocol.md`, `beacon-chain.md`), on the mainnet preset
(`SYNC_COMMITTEE_SIZE` 512):

| Container | Electra and Fulu | Gloas |
|---|---|---|
| `BeaconBlockHeader` | 112 bytes | the same |
| `SyncCommittee` | 512 keys of 48 bytes, and the aggregate: 24,624 bytes | the same |
| `SyncAggregate` | 512 bits and a 96-byte signature: 160 bytes | the same |
| `ExecutionPayloadHeader` | Deneb's 17 fields, `extra_data` up to 32 bytes: 584 to 616 | none |
| `LightClientHeader` | `beacon`, `execution`, a branch of 4: 828 to 860 | `beacon`, `execution_block_hash`, a branch of 11: 496 |
| `LightClientBootstrap` | `header`, `current_sync_committee`, a branch of 6 | branch of 11: 25,472 |
| `LightClientUpdate` | branches of 6 and 7 | branches of 11 and 9: 26,424 |
| `LightClientFinalityUpdate` | a branch of 7 | a branch of 9: 1,448 |
| `LightClientOptimisticUpdate` | `attested_header`, `sync_aggregate`, `signature_slot` | 664 |

A decoder refuses (`none`) exactly what ssz-specs' `deserialize` refuses at the container's
`Desc` (`LeanLightProofs.Ssz`): a size other than a fixed container's, an offset other than the
one canonical position its fixed part allows, offsets out of order or past the end, an
`extra_data` over 32 bytes. It cuts each field out of its input as `deserialize` does
(`Bytes.extract`), so a variable field is decoded from its own copy. `root` is
`hash_tree_root`. Fields hold `Nat` for integers (each below 2⁶⁴, or 2²⁵⁶ for
`base_fee_per_gas`) and `ByteArray` for byte vectors and roots, branches `Array ByteArray`.
-/

namespace LeanLight.Lc.Ssz

open LeanLight.Lc.Bytes (extract)

/-! ## Common containers -/

/-- A `BeaconBlockHeader`. -/
structure BeaconBlockHeader where
  slot : Nat
  proposerIndex : Nat
  parentRoot : ByteArray
  stateRoot : ByteArray
  bodyRoot : ByteArray

namespace BeaconBlockHeader

/-- Its encoded size. -/
def size : Nat := 112

/-- Its fields in `bs`, unchecked. -/
def read (bs : ByteArray) : BeaconBlockHeader :=
  { slot := u64 bs 0, proposerIndex := u64 bs 8, parentRoot := slice bs 16 32,
    stateRoot := slice bs 48 32, bodyRoot := slice bs 80 32 }

/-- A `BeaconBlockHeader` from exactly its 112 bytes. -/
def decode (bs : ByteArray) : Option BeaconBlockHeader :=
  if bs.size = size then some (read bs) else none

/-- `hash_tree_root`: five fields, a tree of depth 3. -/
def root (h : BeaconBlockHeader) : ByteArray :=
  subtree #[u64Root h.slot, u64Root h.proposerIndex, h.parentRoot, h.stateRoot, h.bodyRoot] 3 0

end BeaconBlockHeader

/-- The number of keys in a sync committee (the mainnet preset). -/
abbrev syncCommitteeSize : Nat := 512

/-- A `SyncCommittee`: 512 compressed G1 keys and their aggregate. -/
structure SyncCommittee where
  pubkeys : Array ByteArray
  aggregatePubkey : ByteArray

namespace SyncCommittee

/-- Its encoded size: 513 keys of 48 bytes. -/
def size : Nat := 48 * syncCommitteeSize + 48

/-- Its fields in `bs`, unchecked. -/
def read (bs : ByteArray) : SyncCommittee :=
  { pubkeys := fields bs 0 48 syncCommitteeSize,
    aggregatePubkey := slice bs (48 * syncCommitteeSize) 48 }

/-- A `SyncCommittee` from exactly its 24,624 bytes. -/
def decode (bs : ByteArray) : Option SyncCommittee :=
  if bs.size = size then some (read bs) else none

/-- `hash_tree_root` of a 48-byte key: two nodes. -/
def pubkeyRoot (pk : ByteArray) : ByteArray := bytesRoot pk 1

/-- `hash_tree_root`: the keys' roots in a tree of depth 9, beside the aggregate's root. -/
def root (c : SyncCommittee) : ByteArray :=
  hash64 (subtree (c.pubkeys.map pubkeyRoot) 9 0) (pubkeyRoot c.aggregatePubkey)

end SyncCommittee

/-- A `SyncAggregate`: 512 participation bits and a compressed G2 signature. -/
structure SyncAggregate where
  bits : ByteArray
  signature : ByteArray

namespace SyncAggregate

/-- Its encoded size. -/
def size : Nat := syncCommitteeSize / 8 + 96

/-- Its fields in `bs`, unchecked. -/
def read (bs : ByteArray) : SyncAggregate :=
  { bits := slice bs 0 (syncCommitteeSize / 8), signature := slice bs (syncCommitteeSize / 8) 96 }

/-- A `SyncAggregate` from exactly its 160 bytes. -/
def decode (bs : ByteArray) : Option SyncAggregate :=
  if bs.size = size then some (read bs) else none

/-- `hash_tree_root`: the bits in two nodes, the signature in three (a tree of depth 2). -/
def root (a : SyncAggregate) : ByteArray :=
  hash64 (bytesRoot a.bits 1) (bytesRoot a.signature 2)

end SyncAggregate

/-- `hash_tree_root` of a `Vector[Bytes32, n]` branch, `d` the depth that holds `n` roots. -/
def branchRoot (branch : Array ByteArray) (d : Nat) : ByteArray := subtree branch d 0

/-! ## Electra and Fulu -/

/-- Deneb's `ExecutionPayloadHeader`, which Electra's and Fulu's light-client headers carry. -/
structure ExecutionPayloadHeader where
  parentHash : ByteArray
  feeRecipient : ByteArray
  stateRoot : ByteArray
  receiptsRoot : ByteArray
  logsBloom : ByteArray
  prevRandao : ByteArray
  blockNumber : Nat
  gasLimit : Nat
  gasUsed : Nat
  timestamp : Nat
  extraData : ByteArray
  baseFeePerGas : Nat
  blockHash : ByteArray
  transactionsRoot : ByteArray
  withdrawalsRoot : ByteArray
  blobGasUsed : Nat
  excessBlobGas : Nat

namespace ExecutionPayloadHeader

/-- The size of its fixed part, where `extra_data`'s offset points. -/
def fixedSize : Nat := 584

/-- `MAX_EXTRA_DATA_BYTES`. -/
def maxExtraData : Nat := 32

/-- An `ExecutionPayloadHeader` from its bytes: the fixed part, `extra_data`'s offset equal to
its end, and at most 32 bytes of `extra_data` after it. -/
def decode (bs : ByteArray) : Option ExecutionPayloadHeader :=
  if fixedSize ≤ bs.size ∧ bs.size ≤ fixedSize + maxExtraData ∧ offsetAt bs 436 = fixedSize then
    some {
      parentHash := slice bs 0 32, feeRecipient := slice bs 32 20,
      stateRoot := slice bs 52 32, receiptsRoot := slice bs 84 32, logsBloom := slice bs 116 256,
      prevRandao := slice bs 372 32, blockNumber := u64 bs 404, gasLimit := u64 bs 412,
      gasUsed := u64 bs 420, timestamp := u64 bs 428, extraData := extract bs fixedSize bs.size,
      baseFeePerGas := readLE bs 440 32, blockHash := slice bs 472 32,
      transactionsRoot := slice bs 504 32, withdrawalsRoot := slice bs 536 32,
      blobGasUsed := u64 bs 568, excessBlobGas := u64 bs 576 }
  else none

/-- `hash_tree_root`: seventeen fields, a tree of depth 5; `extra_data`, a `ByteList[32]`, is its
one node mixed with its length. -/
def root (e : ExecutionPayloadHeader) : ByteArray :=
  subtree #[e.parentHash, bytesRoot e.feeRecipient 0, e.stateRoot, e.receiptsRoot,
    bytesRoot e.logsBloom 3, e.prevRandao, u64Root e.blockNumber, u64Root e.gasLimit,
    u64Root e.gasUsed, u64Root e.timestamp,
    mixInLength (bytesRoot e.extraData 0) e.extraData.size, u256Root e.baseFeePerGas,
    e.blockHash, e.transactionsRoot, e.withdrawalsRoot, u64Root e.blobGasUsed,
    u64Root e.excessBlobGas] 5 0

end ExecutionPayloadHeader

namespace Electra

/-- Electra's (and Fulu's) `LightClientHeader`. -/
structure Header where
  beacon : BeaconBlockHeader
  execution : ExecutionPayloadHeader
  executionBranch : Array ByteArray

/-- `ExecutionBranch`: `floorlog2(EXECUTION_PAYLOAD_GINDEX)` roots. -/
def executionBranchLength : Nat := 4
/-- `CurrentSyncCommitteeBranch` and `NextSyncCommitteeBranch`. -/
def syncCommitteeBranchLength : Nat := 6
/-- `FinalityBranch`. -/
def finalityBranchLength : Nat := 7

namespace Header

/-- The size of its fixed part: `beacon`, `execution`'s offset, the branch. -/
def fixedSize : Nat := 244

/-- A `LightClientHeader` from its bytes: `execution` from the fixed part's end to the end. -/
def decode (bs : ByteArray) : Option Header :=
  if fixedSize ≤ bs.size ∧ offsetAt bs 112 = fixedSize then
    match ExecutionPayloadHeader.decode (extract bs fixedSize bs.size) with
    | some execution =>
      some {
        beacon := BeaconBlockHeader.read (slice bs 0 112), execution,
        executionBranch := roots bs 116 executionBranchLength }
    | none => none
  else none

/-- `hash_tree_root`: three fields, a tree of depth 2. -/
def root (h : Header) : ByteArray :=
  subtree #[h.beacon.root, h.execution.root, branchRoot h.executionBranch 2] 2 0

end Header

/-- Electra's `LightClientBootstrap`. -/
structure Bootstrap where
  header : Header
  currentSyncCommittee : SyncCommittee
  currentSyncCommitteeBranch : Array ByteArray

namespace Bootstrap

/-- The size of its fixed part. -/
def fixedSize : Nat := 4 + SyncCommittee.size + 32 * syncCommitteeBranchLength

/-- A `LightClientBootstrap` from its bytes: `header` after the fixed part. -/
def decode (bs : ByteArray) : Option Bootstrap :=
  if fixedSize ≤ bs.size ∧ offsetAt bs 0 = fixedSize then
    match Header.decode (extract bs fixedSize bs.size) with
    | some header =>
      some {
        header, currentSyncCommittee := SyncCommittee.read (slice bs 4 SyncCommittee.size),
        currentSyncCommitteeBranch := roots bs (4 + SyncCommittee.size) syncCommitteeBranchLength }
    | none => none
  else none

/-- `hash_tree_root`: three fields, a tree of depth 2. -/
def root (b : Bootstrap) : ByteArray :=
  subtree #[b.header.root, b.currentSyncCommittee.root,
    branchRoot b.currentSyncCommitteeBranch 3] 2 0

end Bootstrap

/-- Electra's `LightClientUpdate`. -/
structure Update where
  attestedHeader : Header
  nextSyncCommittee : SyncCommittee
  nextSyncCommitteeBranch : Array ByteArray
  finalizedHeader : Header
  finalityBranch : Array ByteArray
  syncAggregate : SyncAggregate
  signatureSlot : Nat

namespace Update

/-- Where `finalized_header`'s offset sits. -/
def finalizedOffsetAt : Nat := 4 + SyncCommittee.size + 32 * syncCommitteeBranchLength

/-- The size of its fixed part. -/
def fixedSize : Nat :=
  finalizedOffsetAt + 4 + 32 * finalityBranchLength + SyncAggregate.size + 8

/-- A `LightClientUpdate` from its bytes: `attested_header` from the fixed part's end to
`finalized_header`'s offset, `finalized_header` from there to the end. -/
def decode (bs : ByteArray) : Option Update :=
  let o₂ := offsetAt bs finalizedOffsetAt
  if fixedSize ≤ bs.size ∧ offsetAt bs 0 = fixedSize ∧ fixedSize ≤ o₂ ∧ o₂ ≤ bs.size then
    match Header.decode (extract bs fixedSize o₂), Header.decode (extract bs o₂ bs.size) with
    | some attestedHeader, some finalizedHeader =>
      let f := finalizedOffsetAt + 4
      some {
        attestedHeader, finalizedHeader,
        nextSyncCommittee := SyncCommittee.read (slice bs 4 SyncCommittee.size),
        nextSyncCommitteeBranch := roots bs (4 + SyncCommittee.size) syncCommitteeBranchLength,
        finalityBranch := roots bs f finalityBranchLength,
        syncAggregate := SyncAggregate.read (slice bs (f + 32 * finalityBranchLength)
          SyncAggregate.size),
        signatureSlot := u64 bs (f + 32 * finalityBranchLength + SyncAggregate.size) }
    | _, _ => none
  else none

/-- `hash_tree_root`: seven fields, a tree of depth 3. -/
def root (u : Update) : ByteArray :=
  subtree #[u.attestedHeader.root, u.nextSyncCommittee.root,
    branchRoot u.nextSyncCommitteeBranch 3, u.finalizedHeader.root,
    branchRoot u.finalityBranch 3, u.syncAggregate.root, u64Root u.signatureSlot] 3 0

end Update

/-- Electra's `LightClientFinalityUpdate`. -/
structure FinalityUpdate where
  attestedHeader : Header
  finalizedHeader : Header
  finalityBranch : Array ByteArray
  syncAggregate : SyncAggregate
  signatureSlot : Nat

namespace FinalityUpdate

/-- The size of its fixed part. -/
def fixedSize : Nat := 8 + 32 * finalityBranchLength + SyncAggregate.size + 8

/-- A `LightClientFinalityUpdate` from its bytes. -/
def decode (bs : ByteArray) : Option FinalityUpdate :=
  let o₂ := offsetAt bs 4
  if fixedSize ≤ bs.size ∧ offsetAt bs 0 = fixedSize ∧ fixedSize ≤ o₂ ∧ o₂ ≤ bs.size then
    match Header.decode (extract bs fixedSize o₂), Header.decode (extract bs o₂ bs.size) with
    | some attestedHeader, some finalizedHeader =>
      some {
        attestedHeader, finalizedHeader, finalityBranch := roots bs 8 finalityBranchLength,
        syncAggregate := SyncAggregate.read (slice bs (8 + 32 * finalityBranchLength)
          SyncAggregate.size),
        signatureSlot := u64 bs (8 + 32 * finalityBranchLength + SyncAggregate.size) }
    | _, _ => none
  else none

/-- `hash_tree_root`: five fields, a tree of depth 3. -/
def root (u : FinalityUpdate) : ByteArray :=
  subtree #[u.attestedHeader.root, u.finalizedHeader.root, branchRoot u.finalityBranch 3,
    u.syncAggregate.root, u64Root u.signatureSlot] 3 0

end FinalityUpdate

/-- Electra's `LightClientOptimisticUpdate`. -/
structure OptimisticUpdate where
  attestedHeader : Header
  syncAggregate : SyncAggregate
  signatureSlot : Nat

namespace OptimisticUpdate

/-- The size of its fixed part. -/
def fixedSize : Nat := 4 + SyncAggregate.size + 8

/-- A `LightClientOptimisticUpdate` from its bytes. -/
def decode (bs : ByteArray) : Option OptimisticUpdate :=
  if fixedSize ≤ bs.size ∧ offsetAt bs 0 = fixedSize then
    match Header.decode (extract bs fixedSize bs.size) with
    | some attestedHeader =>
      some {
        attestedHeader, syncAggregate := SyncAggregate.read (slice bs 4 SyncAggregate.size),
        signatureSlot := u64 bs (4 + SyncAggregate.size) }
    | none => none
  else none

/-- `hash_tree_root`: three fields, a tree of depth 2. -/
def root (u : OptimisticUpdate) : ByteArray :=
  subtree #[u.attestedHeader.root, u.syncAggregate.root, u64Root u.signatureSlot] 2 0

end OptimisticUpdate

end Electra

/-! ## Gloas -/

namespace Gloas

/-- Gloas's `LightClientHeader`: no payload, only `execution_block_hash`. -/
structure Header where
  beacon : BeaconBlockHeader
  executionBlockHash : ByteArray
  executionBranch : Array ByteArray

/-- `ExecutionBranch`: `floorlog2(EXECUTION_BLOCK_HASH_GINDEX_GLOAS)` roots. -/
def executionBranchLength : Nat := 11
/-- `CurrentSyncCommitteeBranch` and `NextSyncCommitteeBranch`. -/
def syncCommitteeBranchLength : Nat := 11
/-- `FinalityBranch`. -/
def finalityBranchLength : Nat := 9

namespace Header

/-- Its encoded size. -/
def size : Nat := BeaconBlockHeader.size + 32 + 32 * executionBranchLength

/-- Its fields in `bs`, unchecked. -/
def read (bs : ByteArray) : Header :=
  { beacon := BeaconBlockHeader.read (slice bs 0 BeaconBlockHeader.size),
    executionBlockHash := slice bs BeaconBlockHeader.size 32,
    executionBranch := roots bs (BeaconBlockHeader.size + 32) executionBranchLength }

/-- A `LightClientHeader` from exactly its 496 bytes. -/
def decode (bs : ByteArray) : Option Header := if bs.size = size then some (read bs) else none

/-- `hash_tree_root`: three fields, a tree of depth 2, the branch's 11 roots at depth 4. -/
def root (h : Header) : ByteArray :=
  subtree #[h.beacon.root, h.executionBlockHash, branchRoot h.executionBranch 4] 2 0

end Header

/-- Gloas's `LightClientBootstrap`. -/
structure Bootstrap where
  header : Header
  currentSyncCommittee : SyncCommittee
  currentSyncCommitteeBranch : Array ByteArray

namespace Bootstrap

/-- Its encoded size. -/
def size : Nat := Header.size + SyncCommittee.size + 32 * syncCommitteeBranchLength

/-- A `LightClientBootstrap` from exactly its 25,472 bytes. -/
def decode (bs : ByteArray) : Option Bootstrap :=
  if bs.size = size then
    some {
      header := Header.read (slice bs 0 Header.size),
      currentSyncCommittee := SyncCommittee.read (slice bs Header.size SyncCommittee.size),
      currentSyncCommitteeBranch :=
        roots bs (Header.size + SyncCommittee.size) syncCommitteeBranchLength }
  else none

/-- `hash_tree_root`: three fields, a tree of depth 2. -/
def root (b : Bootstrap) : ByteArray :=
  subtree #[b.header.root, b.currentSyncCommittee.root,
    branchRoot b.currentSyncCommitteeBranch 4] 2 0

end Bootstrap

/-- Gloas's `LightClientUpdate`. -/
structure Update where
  attestedHeader : Header
  nextSyncCommittee : SyncCommittee
  nextSyncCommitteeBranch : Array ByteArray
  finalizedHeader : Header
  finalityBranch : Array ByteArray
  syncAggregate : SyncAggregate
  signatureSlot : Nat

namespace Update

/-- Where `finalized_header` starts. -/
def finalizedAt : Nat := Header.size + SyncCommittee.size + 32 * syncCommitteeBranchLength

/-- Where `sync_aggregate` starts. -/
def aggregateAt : Nat := finalizedAt + Header.size + 32 * finalityBranchLength

/-- Its encoded size: 26,424 bytes. -/
def size : Nat := aggregateAt + SyncAggregate.size + 8

/-- A `LightClientUpdate` from exactly its 26,424 bytes. -/
def decode (bs : ByteArray) : Option Update :=
  if bs.size = size then
    some {
      attestedHeader := Header.read (slice bs 0 Header.size),
      nextSyncCommittee := SyncCommittee.read (slice bs Header.size SyncCommittee.size),
      nextSyncCommitteeBranch :=
        roots bs (Header.size + SyncCommittee.size) syncCommitteeBranchLength,
      finalizedHeader := Header.read (slice bs finalizedAt Header.size),
      finalityBranch := roots bs (finalizedAt + Header.size) finalityBranchLength,
      syncAggregate := SyncAggregate.read (slice bs aggregateAt SyncAggregate.size),
      signatureSlot := u64 bs (aggregateAt + SyncAggregate.size) }
  else none

/-- `hash_tree_root`: seven fields, a tree of depth 3. -/
def root (u : Update) : ByteArray :=
  subtree #[u.attestedHeader.root, u.nextSyncCommittee.root,
    branchRoot u.nextSyncCommitteeBranch 4, u.finalizedHeader.root,
    branchRoot u.finalityBranch 4, u.syncAggregate.root, u64Root u.signatureSlot] 3 0

end Update

/-- Gloas's `LightClientFinalityUpdate`. -/
structure FinalityUpdate where
  attestedHeader : Header
  finalizedHeader : Header
  finalityBranch : Array ByteArray
  syncAggregate : SyncAggregate
  signatureSlot : Nat

namespace FinalityUpdate

/-- Where `sync_aggregate` starts. -/
def aggregateAt : Nat := 2 * Header.size + 32 * finalityBranchLength

/-- Its encoded size: 1,448 bytes. -/
def size : Nat := aggregateAt + SyncAggregate.size + 8

/-- A `LightClientFinalityUpdate` from exactly its 1,448 bytes. -/
def decode (bs : ByteArray) : Option FinalityUpdate :=
  if bs.size = size then
    some {
      attestedHeader := Header.read (slice bs 0 Header.size),
      finalizedHeader := Header.read (slice bs Header.size Header.size),
      finalityBranch := roots bs (2 * Header.size) finalityBranchLength,
      syncAggregate := SyncAggregate.read (slice bs aggregateAt SyncAggregate.size),
      signatureSlot := u64 bs (aggregateAt + SyncAggregate.size) }
  else none

/-- `hash_tree_root`: five fields, a tree of depth 3. -/
def root (u : FinalityUpdate) : ByteArray :=
  subtree #[u.attestedHeader.root, u.finalizedHeader.root, branchRoot u.finalityBranch 4,
    u.syncAggregate.root, u64Root u.signatureSlot] 3 0

end FinalityUpdate

/-- Gloas's `LightClientOptimisticUpdate`. -/
structure OptimisticUpdate where
  attestedHeader : Header
  syncAggregate : SyncAggregate
  signatureSlot : Nat

namespace OptimisticUpdate

/-- Its encoded size: 664 bytes. -/
def size : Nat := Header.size + SyncAggregate.size + 8

/-- A `LightClientOptimisticUpdate` from exactly its 664 bytes. -/
def decode (bs : ByteArray) : Option OptimisticUpdate :=
  if bs.size = size then
    some {
      attestedHeader := Header.read (slice bs 0 Header.size),
      syncAggregate := SyncAggregate.read (slice bs Header.size SyncAggregate.size),
      signatureSlot := u64 bs (Header.size + SyncAggregate.size) }
  else none

/-- `hash_tree_root`: three fields, a tree of depth 2. -/
def root (u : OptimisticUpdate) : ByteArray :=
  subtree #[u.attestedHeader.root, u.syncAggregate.root, u64Root u.signatureSlot] 2 0

end OptimisticUpdate

end Gloas

end LeanLight.Lc.Ssz
