import LeanLight.Ssz.Merkle
import LeanLight.Ssz.Containers
import LeanLightProofs.Vendor.SszSpecs.Ssz.Type.Paths

/-!
# The light client's generalized indices, recomputed (25b)

Each gindex `LeanLight.Ssz` pins is ssz-specs' `getGeneralizedIndex` of the path to its field, in the
container that holds it, as consensus-specs v1.7.0-beta.4 lays it out: Electra's and Fulu's
`BeaconState` (37 and 38 fields) and `BeaconBlockBody` (13) are bounded containers, where a
field's gindex is `next_pow2(n) + i`; Gloas's `BeaconState` (46 fields), `BeaconBlockBody` (13)
and `ExecutionPayloadBid` (12) are `ProgressiveContainer`s (EIP-7495), every field active, where
it is the field's place on the progressive spine.

The field names are transcribed from the specification (`*/beacon-chain.md`, `class BeaconState`
and the rest), and each theorem states its path by name (`at`), so a reviewer checks the names
and their order against the specification and nothing else: the theorems hold for **every**
choice of the other fields' types, since a gindex depends only on the number of fields, the
position of each field on the path and, for a progressive container, its active fields. The one
type each statement fixes is the field on the path (`HasField`): a `Checkpoint` is `(epoch:
uint64, root: Bytes32)`, the leaf a `Bytes32`.

Every branch length the containers decode is the depth of its gindex (`branch lengths`).
-/

namespace LeanLight.Lc.Ssz

open _root_.Ssz (Desc PathStep getGeneralizedIndex nextPow2 gindexConcat activePosition
  progressiveChunkGindex)

/-! ## The specification's field names -/

/-- `BeaconState`'s fields in Electra (`electra/beacon-chain.md`). -/
def beaconStateElectra : List String :=
  ["genesis_time", "genesis_validators_root", "slot", "fork", "latest_block_header",
   "block_roots", "state_roots", "historical_roots", "eth1_data", "eth1_data_votes",
   "eth1_deposit_index", "validators", "balances", "randao_mixes", "slashings",
   "previous_epoch_participation", "current_epoch_participation", "justification_bits",
   "previous_justified_checkpoint", "current_justified_checkpoint", "finalized_checkpoint",
   "inactivity_scores", "current_sync_committee", "next_sync_committee",
   "latest_execution_payload_header", "next_withdrawal_index", "next_withdrawal_validator_index",
   "historical_summaries", "deposit_requests_start_index", "deposit_balance_to_consume",
   "exit_balance_to_consume", "earliest_exit_epoch", "consolidation_balance_to_consume",
   "earliest_consolidation_epoch", "pending_deposits", "pending_partial_withdrawals",
   "pending_consolidations"]

/-- `BeaconState`'s fields in Fulu (`fulu/beacon-chain.md`): Electra's and `proposer_lookahead`. -/
def beaconStateFulu : List String := beaconStateElectra ++ ["proposer_lookahead"]

/-- `BeaconState`'s fields in Gloas (`gloas/beacon-chain.md`), `active_fields(width=46)`. -/
def beaconStateGloas : List String :=
  ["genesis_time", "genesis_validators_root", "slot", "fork", "latest_block_header",
   "block_roots", "state_roots", "historical_roots", "eth1_data", "eth1_data_votes",
   "eth1_deposit_index", "validators", "balances", "randao_mixes", "slashings",
   "previous_epoch_participation", "current_epoch_participation", "justification_bits",
   "previous_justified_checkpoint", "current_justified_checkpoint", "finalized_checkpoint",
   "inactivity_scores", "current_sync_committee", "next_sync_committee", "latest_block_hash",
   "next_withdrawal_index", "next_withdrawal_validator_index", "historical_summaries",
   "deposit_requests_start_index", "deposit_balance_to_consume", "exit_balance_to_consume",
   "earliest_exit_epoch", "consolidation_balance_to_consume", "earliest_consolidation_epoch",
   "pending_deposits", "pending_partial_withdrawals", "pending_consolidations",
   "proposer_lookahead", "builders", "next_withdrawal_builder_index",
   "execution_payload_availability", "builder_pending_payments", "builder_pending_withdrawals",
   "latest_execution_payload_bid", "payload_expected_withdrawals", "ptc_window"]

/-- `BeaconBlockBody`'s fields in Electra, which Fulu keeps (`electra/beacon-chain.md`). -/
def beaconBlockBodyElectra : List String :=
  ["randao_reveal", "eth1_data", "graffiti", "proposer_slashings", "attester_slashings",
   "attestations", "deposits", "voluntary_exits", "sync_aggregate", "execution_payload",
   "bls_to_execution_changes", "blob_kzg_commitments", "execution_requests"]

/-- `ExecutionPayload`'s fields from Deneb to Fulu (`deneb/beacon-chain.md`). -/
def executionPayloadDeneb : List String :=
  ["parent_hash", "fee_recipient", "state_root", "receipts_root", "logs_bloom", "prev_randao",
   "block_number", "gas_limit", "gas_used", "timestamp", "extra_data", "base_fee_per_gas",
   "block_hash", "transactions", "withdrawals", "blob_gas_used", "excess_blob_gas"]

/-- `BeaconBlockBody`'s fields in Gloas (`gloas/beacon-chain.md`), `active_fields(width=13)`. -/
def beaconBlockBodyGloas : List String :=
  ["randao_reveal", "eth1_data", "graffiti", "proposer_slashings", "attester_slashings",
   "attestations", "deposits", "voluntary_exits", "sync_aggregate", "bls_to_execution_changes",
   "signed_execution_payload_bid", "payload_attestations", "parent_execution_requests"]

/-- `SignedExecutionPayloadBid`'s fields (Gloas). -/
def signedExecutionPayloadBid : List String := ["message", "signature"]

/-- `ExecutionPayloadBid`'s fields (Gloas), `active_fields(width=12)`. -/
def executionPayloadBid : List String :=
  ["parent_block_hash", "parent_block_root", "block_hash", "prev_randao", "fee_recipient",
   "gas_limit", "builder_index", "slot", "value", "execution_payment", "blob_kzg_commitments",
   "execution_requests_root"]

/-- `Checkpoint`'s fields. -/
def checkpointFields : List String := ["epoch", "root"]

/-- `Checkpoint`: `(epoch: uint64, root: Root)`. -/
def checkpoint : Desc := .container checkpointFields [.uint 8, .byteVector 32]

/-- `Bytes32` (and `Hash32`, `Root`). -/
def bytes32 : Desc := .byteVector 32

/-- The path step to the field `name` of a container whose fields are `names`. -/
def at_ (names : List String) (name : String) : PathStep := .position (names.idxOf name)

/-- `fields` has one type per name of `names`, and `name`'s is `f`. -/
structure HasField (names : List String) (fields : List Desc) (name : String) (f : Desc) :
    Prop where
  count : fields.length = names.length
  field : fields[names.idxOf name]? = some f

/-- Every field of a progressive container active: `active_fields(width=n)`. -/
def allActive (n : Nat) : List Bool := List.replicate n true

/-! ## Steps -/

theorem resolveStep_container (names : List String) (fields : List Desc) (i : Nat) (f : Desc)
    (hf : fields[i]? = some f) :
    (Desc.container names fields).resolveStep (.position i) =
      .ok (nextPow2 fields.length + i, some f) := by
  simp [Desc.resolveStep, Desc.chunkPosition, Desc.elementType, hf, Desc.chunkCount,
    bind, Except.bind, pure, Except.pure]

theorem resolveStep_progressive (active : List Bool) (names : List String) (fields : List Desc)
    (i p : Nat) (f : Desc) (hf : fields[i]? = some f) (hp : activePosition active i = some p) :
    (Desc.progressiveContainer active names fields).resolveStep (.position i) =
      .ok (progressiveChunkGindex p, some f) := by
  simp [Desc.resolveStep, Desc.chunkPosition, Desc.elementType, hf, _root_.Ssz.layoutPosition, hp,
    bind, Except.bind, pure, Except.pure]

theorem gindex_cons (shape child : Desc) (step : PathStep) (rest : List PathStep) (i : Nat)
    (h : shape.resolveStep step = .ok (i, some child)) :
    getGeneralizedIndex shape (step :: rest) =
      (getGeneralizedIndex child rest).bind (gindexConcat i) := by
  simp only [getGeneralizedIndex, h, bind, Except.bind]

theorem resolveStep_at (names : List String) (fields : List Desc) (name : String) (f : Desc)
    (h : HasField names fields name f) :
    (Desc.container names fields).resolveStep (at_ names name) =
      .ok (nextPow2 names.length + names.idxOf name, some f) := by
  rw [at_, resolveStep_container _ _ _ _ h.field, h.count]

theorem resolveStep_atP (n : Nat) (names : List String) (fields : List Desc) (name : String)
    (f : Desc) (p : Nat) (h : HasField names fields name f)
    (hp : activePosition (allActive n) (names.idxOf name) = some p) :
    (Desc.progressiveContainer (allActive n) names fields).resolveStep (at_ names name) =
      .ok (progressiveChunkGindex p, some f) := by
  rw [at_, resolveStep_progressive _ _ _ _ _ _ h.field hp]

/-! ## Positions, as the specification lists the fields -/

theorem pos_checkpoint_root : checkpointFields.idxOf "root" = 1 := by decide
theorem pos_finalized_electra : beaconStateElectra.idxOf "finalized_checkpoint" = 20 := by decide
theorem pos_current_electra : beaconStateElectra.idxOf "current_sync_committee" = 22 := by decide
theorem pos_next_electra : beaconStateElectra.idxOf "next_sync_committee" = 23 := by decide
theorem pos_finalized_fulu : beaconStateFulu.idxOf "finalized_checkpoint" = 20 := by decide
theorem pos_current_fulu : beaconStateFulu.idxOf "current_sync_committee" = 22 := by decide
theorem pos_next_fulu : beaconStateFulu.idxOf "next_sync_committee" = 23 := by decide
theorem pos_payload_electra : beaconBlockBodyElectra.idxOf "execution_payload" = 9 := by decide
theorem pos_block_hash_deneb : executionPayloadDeneb.idxOf "block_hash" = 12 := by decide
theorem pos_finalized_gloas : beaconStateGloas.idxOf "finalized_checkpoint" = 20 := by decide
theorem pos_current_gloas : beaconStateGloas.idxOf "current_sync_committee" = 22 := by decide
theorem pos_next_gloas : beaconStateGloas.idxOf "next_sync_committee" = 23 := by decide
theorem pos_bid_gloas : beaconBlockBodyGloas.idxOf "signed_execution_payload_bid" = 10 := by decide
theorem pos_message : signedExecutionPayloadBid.idxOf "message" = 0 := by decide
theorem pos_parent_block_hash : executionPayloadBid.idxOf "parent_block_hash" = 0 := by decide

theorem len_electra : beaconStateElectra.length = 37 := by decide
theorem len_fulu : beaconStateFulu.length = 38 := by decide
theorem len_gloas : beaconStateGloas.length = 46 := by decide
theorem len_body_electra : beaconBlockBodyElectra.length = 13 := by decide
theorem len_payload_deneb : executionPayloadDeneb.length = 17 := by decide
theorem len_body_gloas : beaconBlockBodyGloas.length = 13 := by decide
theorem len_bid : executionPayloadBid.length = 12 := by decide
theorem len_signed_bid : signedExecutionPayloadBid.length = 2 := by decide
theorem len_checkpoint : checkpointFields.length = 2 := by decide

/-- `root` in a `Checkpoint`: its second of two fields. -/
theorem gindex_checkpoint_root :
    getGeneralizedIndex checkpoint [at_ checkpointFields "root"] = .ok 3 := by
  rw [checkpoint, gindex_cons _ _ _ _ _
    (resolveStep_at _ [.uint 8, .byteVector 32] _ bytes32 ⟨rfl, by rw [pos_checkpoint_root]; rfl⟩)]
  simp [getGeneralizedIndex, nextPow2, _root_.Ssz.depthFor, gindexConcat, _root_.Ssz.gindexDepth,
    pos_checkpoint_root, len_checkpoint, Except.bind, bind, pure, Except.pure]

/-- The arithmetic the theorems below end on. -/
macro "gindex_arith" : tactic => `(tactic|
  simp [getGeneralizedIndex, nextPow2, _root_.Ssz.depthFor, progressiveChunkGindex, gindexConcat,
    _root_.Ssz.gindexDepth, Except.bind, bind, pure, Except.pure, pos_finalized_electra,
    pos_current_electra, pos_next_electra, pos_finalized_fulu, pos_current_fulu, pos_next_fulu,
    pos_payload_electra, pos_block_hash_deneb, len_electra, len_fulu, len_body_electra,
    len_payload_deneb, len_signed_bid, pos_finalized_gloas, pos_current_gloas, pos_next_gloas,
    pos_bid_gloas, pos_message, pos_parent_block_hash, gindexFinalizedRootElectra,
    gindexCurrentSyncCommitteeElectra, gindexNextSyncCommitteeElectra, gindexExecutionPayload,
    gindexExecutionBlockHashDeneb, gindexFinalizedRootGloas, gindexCurrentSyncCommitteeGloas,
    gindexNextSyncCommitteeGloas, gindexExecutionBlockHashGloas])

/-! ## Electra and Fulu -/

/-- `FINALIZED_ROOT_GINDEX_ELECTRA`: `finalized_checkpoint.root` in an Electra `BeaconState`,
whatever its other fields' types. -/
theorem gindexFinalizedRootElectra_eq (fields : List Desc)
    (h : HasField beaconStateElectra fields "finalized_checkpoint" checkpoint) :
    getGeneralizedIndex (.container beaconStateElectra fields)
      [at_ beaconStateElectra "finalized_checkpoint", at_ checkpointFields "root"] =
      .ok gindexFinalizedRootElectra := by
  rw [gindex_cons _ _ _ _ _ (resolveStep_at _ _ _ _ h), gindex_checkpoint_root]
  gindex_arith

/-- `CURRENT_SYNC_COMMITTEE_GINDEX_ELECTRA`. -/
theorem gindexCurrentSyncCommitteeElectra_eq (fields : List Desc) (c : Desc)
    (h : HasField beaconStateElectra fields "current_sync_committee" c) :
    getGeneralizedIndex (.container beaconStateElectra fields)
      [at_ beaconStateElectra "current_sync_committee"] =
      .ok gindexCurrentSyncCommitteeElectra := by
  rw [gindex_cons _ _ _ _ _ (resolveStep_at _ _ _ _ h)]
  gindex_arith

/-- `NEXT_SYNC_COMMITTEE_GINDEX_ELECTRA`. -/
theorem gindexNextSyncCommitteeElectra_eq (fields : List Desc) (c : Desc)
    (h : HasField beaconStateElectra fields "next_sync_committee" c) :
    getGeneralizedIndex (.container beaconStateElectra fields)
      [at_ beaconStateElectra "next_sync_committee"] =
      .ok gindexNextSyncCommitteeElectra := by
  rw [gindex_cons _ _ _ _ _ (resolveStep_at _ _ _ _ h)]
  gindex_arith

/-- Fulu's `BeaconState` (38 fields, still within 64) gives Electra's three indices. -/
theorem gindexFulu_eq (fields : List Desc) (c n : Desc)
    (hf : HasField beaconStateFulu fields "finalized_checkpoint" checkpoint)
    (hc : HasField beaconStateFulu fields "current_sync_committee" c)
    (hn : HasField beaconStateFulu fields "next_sync_committee" n) :
    getGeneralizedIndex (.container beaconStateFulu fields)
        [at_ beaconStateFulu "finalized_checkpoint", at_ checkpointFields "root"] =
        .ok gindexFinalizedRootElectra ∧
      getGeneralizedIndex (.container beaconStateFulu fields)
        [at_ beaconStateFulu "current_sync_committee"] = .ok gindexCurrentSyncCommitteeElectra ∧
      getGeneralizedIndex (.container beaconStateFulu fields)
        [at_ beaconStateFulu "next_sync_committee"] = .ok gindexNextSyncCommitteeElectra := by
  refine ⟨?_, ?_, ?_⟩
  · rw [gindex_cons _ _ _ _ _ (resolveStep_at _ _ _ _ hf), gindex_checkpoint_root]
    gindex_arith
  · rw [gindex_cons _ _ _ _ _ (resolveStep_at _ _ _ _ hc)]
    gindex_arith
  · rw [gindex_cons _ _ _ _ _ (resolveStep_at _ _ _ _ hn)]
    gindex_arith

/-- `EXECUTION_PAYLOAD_GINDEX`: `execution_payload` in an Electra (or Fulu) `BeaconBlockBody`. -/
theorem gindexExecutionPayload_eq (fields : List Desc) (p : Desc)
    (h : HasField beaconBlockBodyElectra fields "execution_payload" p) :
    getGeneralizedIndex (.container beaconBlockBodyElectra fields)
      [at_ beaconBlockBodyElectra "execution_payload"] = .ok gindexExecutionPayload := by
  rw [gindex_cons _ _ _ _ _ (resolveStep_at _ _ _ _ h)]
  gindex_arith

/-- `EXECUTION_BLOCK_HASH_GINDEX_DENEB`: `execution_payload.block_hash` in an Electra (or Fulu)
`BeaconBlockBody`, the payload being Deneb's 17 fields. -/
theorem gindexExecutionBlockHashDeneb_eq (fields payload : List Desc)
    (hp : HasField executionPayloadDeneb payload "block_hash" bytes32)
    (h : HasField beaconBlockBodyElectra fields "execution_payload"
      (.container executionPayloadDeneb payload)) :
    getGeneralizedIndex (.container beaconBlockBodyElectra fields)
      [at_ beaconBlockBodyElectra "execution_payload", at_ executionPayloadDeneb "block_hash"] =
      .ok gindexExecutionBlockHashDeneb := by
  rw [gindex_cons _ _ _ _ _ (resolveStep_at _ _ _ _ h),
    gindex_cons _ _ _ _ _ (resolveStep_at _ _ _ _ hp)]
  gindex_arith

/-! ## Gloas -/

/-- `FINALIZED_ROOT_GINDEX_GLOAS`: `finalized_checkpoint.root` in Gloas's progressive
`BeaconState`. -/
theorem gindexFinalizedRootGloas_eq (fields : List Desc)
    (h : HasField beaconStateGloas fields "finalized_checkpoint" checkpoint) :
    getGeneralizedIndex (.progressiveContainer (allActive 46) beaconStateGloas fields)
      [at_ beaconStateGloas "finalized_checkpoint", at_ checkpointFields "root"] =
      .ok gindexFinalizedRootGloas := by
  rw [gindex_cons _ _ _ _ _ (resolveStep_atP _ _ _ _ _ 20 h (by decide)), gindex_checkpoint_root]
  gindex_arith

/-- `CURRENT_SYNC_COMMITTEE_GINDEX_GLOAS`. -/
theorem gindexCurrentSyncCommitteeGloas_eq (fields : List Desc) (c : Desc)
    (h : HasField beaconStateGloas fields "current_sync_committee" c) :
    getGeneralizedIndex (.progressiveContainer (allActive 46) beaconStateGloas fields)
      [at_ beaconStateGloas "current_sync_committee"] = .ok gindexCurrentSyncCommitteeGloas := by
  rw [gindex_cons _ _ _ _ _ (resolveStep_atP _ _ _ _ _ 22 h (by decide))]
  gindex_arith

/-- `NEXT_SYNC_COMMITTEE_GINDEX_GLOAS`. -/
theorem gindexNextSyncCommitteeGloas_eq (fields : List Desc) (c : Desc)
    (h : HasField beaconStateGloas fields "next_sync_committee" c) :
    getGeneralizedIndex (.progressiveContainer (allActive 46) beaconStateGloas fields)
      [at_ beaconStateGloas "next_sync_committee"] = .ok gindexNextSyncCommitteeGloas := by
  rw [gindex_cons _ _ _ _ _ (resolveStep_atP _ _ _ _ _ 23 h (by decide))]
  gindex_arith

/-- `EXECUTION_BLOCK_HASH_GINDEX_GLOAS`: `signed_execution_payload_bid.message.parent_block_hash`
in Gloas's progressive `BeaconBlockBody`, the bid a progressive container of 12 fields. -/
theorem gindexExecutionBlockHashGloas_eq (fields bid : List Desc) (signature : Desc)
    (hb : HasField executionPayloadBid bid "parent_block_hash" bytes32)
    (h : HasField beaconBlockBodyGloas fields "signed_execution_payload_bid"
      (.container signedExecutionPayloadBid
        [.progressiveContainer (allActive 12) executionPayloadBid bid, signature])) :
    getGeneralizedIndex (.progressiveContainer (allActive 13) beaconBlockBodyGloas fields)
      [at_ beaconBlockBodyGloas "signed_execution_payload_bid",
        at_ signedExecutionPayloadBid "message", at_ executionPayloadBid "parent_block_hash"] =
      .ok gindexExecutionBlockHashGloas := by
  rw [gindex_cons _ _ _ _ _ (resolveStep_atP _ _ _ _ _ 10 h (by decide)),
    gindex_cons _ _ _ _ _ (resolveStep_at _ _ _ _ ⟨rfl, by rw [pos_message]; rfl⟩),
    gindex_cons _ _ _ _ _ (resolveStep_atP _ _ _ _ _ 0 hb (by decide))]
  gindex_arith

/-! ## Branch lengths -/

/-- Each branch the containers decode is as long as its gindex is deep (`floorlog2`). -/
theorem branch_lengths :
    Electra.executionBranchLength = gindexExecutionPayload.log2 ∧
    Electra.syncCommitteeBranchLength = gindexCurrentSyncCommitteeElectra.log2 ∧
    Electra.syncCommitteeBranchLength = gindexNextSyncCommitteeElectra.log2 ∧
    Electra.finalityBranchLength = gindexFinalizedRootElectra.log2 ∧
    Gloas.executionBranchLength = gindexExecutionBlockHashGloas.log2 ∧
    Gloas.syncCommitteeBranchLength = gindexCurrentSyncCommitteeGloas.log2 ∧
    Gloas.syncCommitteeBranchLength = gindexNextSyncCommitteeGloas.log2 ∧
    Gloas.finalityBranchLength = gindexFinalizedRootGloas.log2 := by
  decide

end LeanLight.Lc.Ssz
