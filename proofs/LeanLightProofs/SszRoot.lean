import LeanLight.Ssz.Containers
import LeanLightProofs.SszMerkle
import LeanLightProofs.Vendor.SszSpecs.Ssz.Proofs.Codec.RootLaws
import LeanLightProofs.Vendor.SszSpecs.Ssz.Proofs.Codec.Canonicality
import LeanLightProofs.SszGindex

/-!
# The light client's `hash_tree_root` is ssz-specs' (25b)

For each light-client container, `LeanLight.Ssz`'s `root` of a typed value is ssz-specs'
`hashTreeRoot` of the value it denotes (`toValue`) at the container's `Desc`, transcribed here
from consensus-specs v1.7.0-beta.4: `BeaconBlockHeader.root_eq` and the rest. Each holds of a
value that fits its type (`Fits`: integers below 2⁶⁴, roots of 32 bytes, 512 keys of 48 bytes, at
most 32 bytes of `extra_data`, branches of the type's length), which every value the decoders
return does (`LeanLightProofs.SszDecode`).

The generic steps are ssz-specs' own: a container's root is the bounded tree over its fields'
roots (`htr_container`), a vector of composite elements likewise (`htr_vector`), a basic value or
a byte vector its packed nodes (`htr_uint`, `htr_byteVector`), a `ByteList` its nodes mixed with
its length (`htr_byteList`), a `Bitvector` its packed bits (`htr_bitVector`).
-/

namespace LeanLight.Lc.Ssz

open _root_.Ssz (Bytes Desc Value hashTreeRoot hashTreeRootAt subtreeAt depthFor packBytes
  uintBytes mixIn lengthWord merkleLayout)

/-! ## Generic steps -/

theorem mapM_slots (b : Nat) (l : List (Desc × Value)) (hb : ∀ p ∈ l, p.1.nesting ≤ b) :
    ((l.map some).mapM fun slot => match slot with
      | none => pure _root_.Ssz.zeroChunk
      | some (shape, value) => hashTreeRootAt b shape value) =
      l.mapM (fun p => hashTreeRoot p.1 p.2) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons, List.mapM_cons]
    rw [ih (fun q hq => hb q (List.mem_cons_of_mem _ hq)),
      _root_.Ssz.hashTreeRootAt_eq_hashTreeRoot _ _ _ (hb p List.mem_cons_self)]

theorem nesting_le_deepest (fields : List Desc) :
    ∀ f ∈ fields, f.nesting ≤ Desc.deepestNesting fields := by
  intro f hf
  induction fields with
  | nil => simp at hf
  | cons g gs ih =>
    simp only [Desc.deepestNesting]
    rcases List.mem_cons.mp hf with rfl | h
    · omega
    · have := ih h; omega

/-- A container's root: the bounded tree over its fields' roots. -/
theorem htr_container (names : List String) (fields : List Desc) (values : List Value)
    (rs : List Bytes) (hlen : fields.length = values.length)
    (hm : (fields.zip values).mapM (fun p => hashTreeRoot p.1 p.2) = .ok rs)
    (hcap : rs.length ≤ fields.length) :
    hashTreeRoot (.container names fields) (.seq values) =
      .ok (subtreeAt rs.toArray (depthFor fields.length) 0) := by
  have hb : ∀ p ∈ fields.zip values, p.1.nesting ≤ Desc.deepestNesting fields := by
    intro p hp
    exact nesting_le_deepest fields p.1 (List.of_mem_zip hp).1
  simp only [hashTreeRoot, Desc.nesting, hashTreeRootAt, merkleLayout, hlen, bne_self_eq_false,
    Bool.false_eq_true, ite_false, _root_.Ssz.layoutChunksAt, _root_.Ssz.Leaves.count,
    List.drop_zero, Nat.sub_zero]
  simp only [pure_bind, _root_.Ssz.MerkleLayout.nesting, Option.getD, List.length_map,
    List.length_zip, ← hlen, Nat.min_self]
  rw [List.take_of_length_le (by simp [hlen])]
  erw [mapM_slots _ _ hb, hm]
  simp only [bind_pure_comp, Except.map, Except.bind, bind, _root_.Ssz.merkleizeBounded,
    List.size_toArray]
  simp [show ¬ fields.length < rs.length by omega, pure, Except.pure]

theorem mapM_elements (b : Nat) (e : Desc) (l : List Value) (hb : e.nesting ≤ b) :
    ((l.map fun v => some (e, v)).mapM fun slot => match slot with
      | none => pure _root_.Ssz.zeroChunk
      | some (shape, value) => hashTreeRootAt b shape value) =
      l.mapM (hashTreeRoot e) := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    simp only [List.map_cons, List.mapM_cons]
    rw [ih, _root_.Ssz.hashTreeRootAt_eq_hashTreeRoot _ _ _ hb]

/-- A vector of composite elements: the bounded tree over their roots. -/
theorem htr_vector (e : Desc) (n : Nat) (vs : List Value) (rs : List Bytes)
    (he : e.isBasic = false) (hlen : vs.length = n) (hm : vs.mapM (hashTreeRoot e) = .ok rs)
    (hcap : rs.length ≤ n) :
    hashTreeRoot (.vector e n) (.seq vs) = .ok (subtreeAt rs.toArray (depthFor n) 0) := by
  subst hlen
  simp only [hashTreeRoot, Desc.nesting, hashTreeRootAt, merkleLayout, bne_self_eq_false,
    Bool.false_eq_true, ite_false, _root_.Ssz.sequenceLayout, he, _root_.Ssz.layoutChunksAt,
    _root_.Ssz.Leaves.count, List.drop_zero, Nat.sub_zero]
  simp only [pure_bind, bind_pure_comp, _root_.Ssz.MerkleLayout.nesting, Option.getD,
    List.length_map]
  rw [List.take_of_length_le (by simp)]
  erw [mapM_elements _ _ _ (Nat.le_refl _), hm]
  simp only [Except.map, Except.bind, bind, _root_.Ssz.merkleizeBounded, List.size_toArray]
  simp [Functor.map, Except.map, show ¬ vs.length < rs.length by omega, pure, Except.pure]

theorem extract_packBytes (d : Bytes) :
    (packBytes d).extract 0 ((d.size + 31) / _root_.Ssz.bytesPerChunk) = packBytes d := by
  apply Array.extract_eq_self_of_le
  simp [packBytes]

/-- A `uint` of `w` bytes: its little-endian bytes, packed. -/
theorem htr_uint (w n : Nat) (hn : n < 2 ^ (8 * w)) :
    hashTreeRoot (.uint w) (.uint n) = .ok (subtreeAt (packBytes (uintBytes w n))
      (depthFor (packBytes (uintBytes w n)).size) 0) := by
  simp [hashTreeRoot, Desc.nesting, hashTreeRootAt, merkleLayout, _root_.Ssz.fixedLeaf,
    _root_.Ssz.serialize, hn, _root_.Ssz.MerkleLayout.packing, _root_.Ssz.layoutChunksAt,
    _root_.Ssz.Leaves.count, _root_.Ssz.merkleizeBounded, bind, Except.bind, pure, Except.pure,
    extract_packBytes]

/-- A `ByteVector`: its bytes, packed. -/
theorem htr_byteVector (k : Nat) (d : Bytes) (hd : d.size = k) :
    hashTreeRoot (.byteVector k) (.bytes d) =
      .ok (subtreeAt (packBytes d) (depthFor (packBytes d).size) 0) := by
  subst hd
  simp [hashTreeRoot, Desc.nesting, hashTreeRootAt, merkleLayout, _root_.Ssz.layoutChunksAt,
    _root_.Ssz.Leaves.count, _root_.Ssz.merkleizeBounded, bind, Except.bind, pure, Except.pure,
    _root_.Ssz.MerkleLayout.packing, extract_packBytes]

theorem packBytes_size (d : Bytes) : (packBytes d).size = (d.size + 31) / 32 := by
  simp [packBytes]

/-- A `ByteList[lim]`: its bytes packed into a tree of `lim`'s nodes, mixed with its length. -/
theorem htr_byteList (lim : Nat) (d : Bytes) (hd : d.size ≤ lim) :
    hashTreeRoot (.byteList lim) (.bytes d) = .ok (mixIn (subtreeAt (packBytes d)
      (depthFor (_root_.Ssz.chunksForBytes lim)) 0) (lengthWord d.size)) := by
  have hcap : ¬ _root_.Ssz.chunksForBytes lim < (packBytes d).size := by
    rw [packBytes_size, _root_.Ssz.chunksForBytes]
    exact Nat.not_lt.mpr (Nat.div_le_div_right (by simp only [_root_.Ssz.bytesPerChunk]; omega))
  simp [hashTreeRoot, Desc.nesting, hashTreeRootAt, merkleLayout, _root_.Ssz.layoutChunksAt,
    _root_.Ssz.Leaves.count, _root_.Ssz.merkleizeBounded, bind, Except.bind, pure, Except.pure,
    _root_.Ssz.MerkleLayout.packing, show ¬ lim < d.size by omega, extract_packBytes]
  have hcap' : ¬ _root_.Ssz.chunksForBytes lim < (d.size + 31) / _root_.Ssz.bytesPerChunk := by
    simp only [_root_.Ssz.chunksForBytes, _root_.Ssz.bytesPerChunk]
    exact Nat.not_lt.mpr (Nat.div_le_div_right (by omega))
  simp [hcap']

/-- A `Bitvector[n]`: its bits packed. -/
theorem htr_bitVector (n : Nat) (bits : Array Bool) (hb : bits.size = n)
    (hcap : (_root_.Ssz.packedBits bits).size ≤ _root_.Ssz.chunksForBits n) :
    hashTreeRoot (.bitVector n) (.bits bits) = .ok (subtreeAt (_root_.Ssz.packedBits bits)
      (depthFor (_root_.Ssz.chunksForBits n)) 0) := by
  subst hb
  simp [hashTreeRoot, Desc.nesting, hashTreeRootAt, merkleLayout, _root_.Ssz.layoutChunksAt,
    _root_.Ssz.Leaves.count, _root_.Ssz.merkleizeBounded, bind, Except.bind, pure, Except.pure,
    _root_.Ssz.MerkleLayout.packing, Nat.not_lt.mpr hcap]

/-! ## Leaves, in the runtime's terms -/

theorem uintBytes_size (w v : Nat) : (uintBytes w v).size = w := by
  induction w generalizing v with
  | zero => rfl
  | succ w ih => simp [uintBytes, ih, Nat.add_comm]

theorem htr_u64 (n : Nat) (hn : n < 2 ^ 64) :
    hashTreeRoot (.uint 8) (.uint n) = .ok (u64Root n).data := by
  rw [htr_uint 8 n hn, packBytes_size, uintBytes_size]
  simp only [u64Root, bytesRoot]
  rw [subtree_data _ 0 (by decide), pack_data, leBytes_data]
  simp [depthFor]

theorem htr_u256 (n : Nat) (hn : n < 2 ^ 256) :
    hashTreeRoot (.uint 32) (.uint n) = .ok (u256Root n).data := by
  rw [htr_uint 32 n hn, packBytes_size, uintBytes_size]
  simp only [u256Root, bytesRoot]
  rw [subtree_data _ 0 (by decide), pack_data, leBytes_data]
  simp [depthFor]

/-- A byte vector of `k` bytes whose packed tree has depth `d`. -/
theorem htr_bytes (b : ByteArray) (k d : Nat) (hk : b.size = k)
    (hd : depthFor ((k + 31) / 32) = d) (h64 : d ≤ 64) :
    hashTreeRoot (.byteVector k) (.bytes b.data) = .ok (bytesRoot b d).data := by
  rw [htr_byteVector k b.data (by simpa using hk), packBytes_size, show b.data.size = k by simpa using hk,
    hd, bytesRoot, subtree_data _ _ h64, pack_data]

/-- A 32-byte root is its own root. -/
theorem bytesRoot_32 (b : ByteArray) (hb : b.size = 32) : bytesRoot b 0 = b := by
  have hd : b.data.size = 32 := by simpa using hb
  have hp : pack b = #[b] := by
    apply Array.ext
    · simp [pack, hb, chunkSize]
    · intro i h₁ _
      have hi : i = 0 := by simp [pack, hb, chunkSize] at h₁; omega
      subst hi
      simp only [pack, Array.getElem_ofFn, Nat.zero_mul, Nat.zero_add]
      apply ByteArray.ext
      have he : (Bytes.extract b 0 chunkSize).data = b.data := by
        apply Array.toList_inj.mp
        rw [Bytes.extract_eq, List.drop_zero, List.take_of_length_le (by simp [hd, chunkSize])]
      simp [ByteArray.data_append, he, ← ByteArray.size_data, hd, chunkSize]
  simp [bytesRoot, hp, subtree]

theorem htr_root32 (b : ByteArray) (hb : b.size = 32) :
    hashTreeRoot bytes32 (.bytes b.data) = .ok b.data := by
  rw [bytes32, htr_bytes b 32 0 hb (by simp [depthFor]) (by decide), bytesRoot_32 b hb]

theorem mapM_map_ok {α β γ ε : Type} (l : List α) (g : α → β) (f : β → Except ε γ) (k : α → γ)
    (h : ∀ x ∈ l, f (g x) = .ok (k x)) : (l.map g).mapM f = .ok (l.map k) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, List.mapM_cons, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    rfl

theorem depthFor_512 : depthFor 512 = 9 := by simp [depthFor]

/-! ## The containers, as consensus-specs v1.7.0-beta.4 declares them -/

/-- `Vector[Bytes32, n]`, a Merkle branch. -/
def branchDesc (n : Nat) : Desc := .vector bytes32 n

/-- `BeaconBlockHeader`. -/
def beaconBlockHeaderDesc : Desc :=
  .container ["slot", "proposer_index", "parent_root", "state_root", "body_root"]
    [.uint 8, .uint 8, bytes32, bytes32, bytes32]

/-- `SyncCommittee`, mainnet preset: `pubkeys: Vector[BLSPubkey, 512]`, `aggregate_pubkey`. -/
def syncCommitteeDesc : Desc :=
  .container ["pubkeys", "aggregate_pubkey"] [.vector (.byteVector 48) 512, .byteVector 48]

/-- `SyncAggregate`, mainnet preset. -/
def syncAggregateDesc : Desc :=
  .container ["sync_committee_bits", "sync_committee_signature"] [.bitVector 512, .byteVector 96]

/-- `Vector[Bytes32, n]` as a value. -/
def branchValue (b : Array ByteArray) : Value := .seq (b.toList.map fun r => .bytes r.data)

/-- A branch of `n` 32-byte roots. -/
def BranchFits (b : Array ByteArray) (n : Nat) : Prop := b.size = n ∧ ∀ r ∈ b, r.size = 32

theorem htr_branch (b : Array ByteArray) (n d : Nat) (hb : BranchFits b n)
    (hd : depthFor n = d) (h64 : d ≤ 64) :
    hashTreeRoot (branchDesc n) (branchValue b) = .ok (branchRoot b d).data := by
  rw [branchDesc, branchValue, htr_vector bytes32 n _ (b.toList.map (·.data)) rfl
    (by simpa using hb.1) (mapM_map_ok _ _ _ _ (fun r hr => htr_root32 r (hb.2 r
      (Array.mem_toList_iff.mp hr)))) (by simp [hb.1]), hd, branchRoot, subtree_data _ _ h64]
  congr 2
  apply Array.toList_inj.mp
  simp [nodes]

/-- The value a `BeaconBlockHeader` denotes. -/
def BeaconBlockHeader.toValue (h : BeaconBlockHeader) : Value :=
  .seq [.uint h.slot, .uint h.proposerIndex, .bytes h.parentRoot.data, .bytes h.stateRoot.data,
    .bytes h.bodyRoot.data]

/-- A `BeaconBlockHeader` that fits its type. -/
structure BeaconBlockHeader.Fits (h : BeaconBlockHeader) : Prop where
  slot : h.slot < 2 ^ 64
  proposerIndex : h.proposerIndex < 2 ^ 64
  parentRoot : h.parentRoot.size = 32
  stateRoot : h.stateRoot.size = 32
  bodyRoot : h.bodyRoot.size = 32

/-- `BeaconBlockHeader.root` is `hash_tree_root`. -/
theorem BeaconBlockHeader.root_eq (h : BeaconBlockHeader) (hf : h.Fits) :
    hashTreeRoot beaconBlockHeaderDesc h.toValue = .ok h.root.data := by
  rw [beaconBlockHeaderDesc, toValue, htr_container _ _ _
    [(u64Root h.slot).data, (u64Root h.proposerIndex).data, h.parentRoot.data, h.stateRoot.data,
      h.bodyRoot.data] rfl (by
        simp only [List.zip, List.zipWith, List.mapM_cons, List.mapM_nil, htr_u64 _ hf.slot,
          htr_u64 _ hf.proposerIndex, htr_root32 _ hf.parentRoot, htr_root32 _ hf.stateRoot,
          htr_root32 _ hf.bodyRoot]
        rfl) (by simp)]
  simp only [root, subtree_data _ 3 (by decide)]
  simp [nodes, depthFor]

/-- The value a `SyncCommittee` denotes. -/
def SyncCommittee.toValue (c : SyncCommittee) : Value :=
  .seq [.seq (c.pubkeys.toList.map fun k => .bytes k.data), .bytes c.aggregatePubkey.data]

/-- A `SyncCommittee` that fits its type: 512 keys of 48 bytes, and a 48-byte aggregate. -/
structure SyncCommittee.Fits (c : SyncCommittee) : Prop where
  count : c.pubkeys.size = syncCommitteeSize
  keys : ∀ k ∈ c.pubkeys, k.size = 48
  aggregate : c.aggregatePubkey.size = 48

theorem htr_pubkey (k : ByteArray) (hk : k.size = 48) :
    hashTreeRoot (.byteVector 48) (.bytes k.data) = .ok (SyncCommittee.pubkeyRoot k).data :=
  htr_bytes k 48 1 hk (by simp [depthFor]) (by decide)

/-- `SyncCommittee.root` is `hash_tree_root`. -/
theorem SyncCommittee.root_eq (c : SyncCommittee) (hf : c.Fits) :
    hashTreeRoot syncCommitteeDesc c.toValue = .ok c.root.data := by
  have hv : hashTreeRoot (.vector (.byteVector 48) 512)
      (.seq (c.pubkeys.toList.map fun k => .bytes k.data)) =
      .ok (subtree (c.pubkeys.map pubkeyRoot) 9 0).data := by
    rw [htr_vector _ 512 _ (c.pubkeys.toList.map fun k => (pubkeyRoot k).data) rfl
      (by simpa using hf.count) (mapM_map_ok _ _ _ _ (fun k hk => htr_pubkey k (hf.keys k
        (Array.mem_toList_iff.mp hk)))) (by simp [hf.count]), subtree_data _ 9 (by decide)]
    simp only [depthFor_512]
    congr 2
    apply Array.toList_inj.mp
    simp [nodes]
  rw [syncCommitteeDesc, toValue, htr_container _ _ _
    [(subtree (c.pubkeys.map pubkeyRoot) 9 0).data, (pubkeyRoot c.aggregatePubkey).data] rfl (by
      simp only [List.zip, List.zipWith, List.mapM_cons, List.mapM_nil, hv,
        htr_pubkey _ hf.aggregate]
      rfl) (by simp)]
  simp only [root, hash64_data]
  simp [depthFor, _root_.Ssz.subtreeAt, _root_.Ssz.padded]

/-- The 512 bits of a `Bitvector[512]`, unpacked and packed again, are the 64 bytes they came
from: ssz-specs' canonicality of `deserialize` at `Bitvector[512]`. -/
theorem packBits_unpackBits_512 (d : Bytes) (hd : d.size = 64) :
    _root_.Ssz.packBits (_root_.Ssz.unpackBits d 512) 64 = d := by
  have hdes : _root_.Ssz.deserialize (.bitVector 512) d =
      .ok (.bits (_root_.Ssz.unpackBits d 512)) := by
    simp [_root_.Ssz.deserialize, hd, bind, Except.bind, pure, Except.pure]
  have hser := _root_.Ssz.canonical_bitVector hdes
  simp [_root_.Ssz.serialize, _root_.Ssz.unpackBits] at hser
  exact hser

/-- The value a `SyncAggregate` denotes: its bits unpacked, as `deserialize` reads them. -/
def SyncAggregate.toValue (a : SyncAggregate) : Value :=
  .seq [.bits (_root_.Ssz.unpackBits a.bits.data 512), .bytes a.signature.data]

/-- A `SyncAggregate` that fits its type. -/
structure SyncAggregate.Fits (a : SyncAggregate) : Prop where
  bits : a.bits.size = 64
  signature : a.signature.size = 96

/-- `SyncAggregate.root` is `hash_tree_root`. -/
theorem SyncAggregate.root_eq (a : SyncAggregate) (hf : a.Fits) :
    hashTreeRoot syncAggregateDesc a.toValue = .ok a.root.data := by
  have hd : a.bits.data.size = 64 := by simpa using hf.bits
  have hsize : (_root_.Ssz.unpackBits a.bits.data 512).size = 512 := by
    simp [_root_.Ssz.unpackBits]
  have hpack : _root_.Ssz.packedBits (_root_.Ssz.unpackBits a.bits.data 512) =
      packBytes a.bits.data := by
    rw [_root_.Ssz.packedBits, hsize, show (512 + 7) / 8 = 64 from rfl,
      packBits_unpackBits_512 _ hd]
  have hb : hashTreeRoot (.bitVector 512) (.bits (_root_.Ssz.unpackBits a.bits.data 512)) =
      .ok (bytesRoot a.bits 1).data := by
    rw [htr_bitVector 512 _ hsize (by rw [hpack, packBytes_size, hd]; decide), hpack, bytesRoot,
      subtree_data _ 1 (by decide), pack_data, show _root_.Ssz.chunksForBits 512 = 2 from rfl]
    simp [depthFor]
  rw [syncAggregateDesc, toValue, htr_container _ _ _
    [(bytesRoot a.bits 1).data, (bytesRoot a.signature 2).data] rfl (by
      simp only [List.zip, List.zipWith, List.mapM_cons, List.mapM_nil, hb,
        htr_bytes a.signature 96 2 hf.signature (by simp [depthFor]) (by decide)]
      rfl) (by simp)]
  simp only [root, hash64_data]
  simp [depthFor, _root_.Ssz.subtreeAt, _root_.Ssz.padded]

/-- Deneb's `ExecutionPayloadHeader`, which Electra's and Fulu's light-client headers carry. -/
def executionPayloadHeaderDesc : Desc :=
  .container ["parent_hash", "fee_recipient", "state_root", "receipts_root", "logs_bloom",
      "prev_randao", "block_number", "gas_limit", "gas_used", "timestamp", "extra_data",
      "base_fee_per_gas", "block_hash", "transactions_root", "withdrawals_root", "blob_gas_used",
      "excess_blob_gas"]
    [bytes32, .byteVector 20, bytes32, bytes32, .byteVector 256, bytes32, .uint 8, .uint 8, .uint 8,
      .uint 8, .byteList 32, .uint 32, bytes32, bytes32, bytes32, .uint 8, .uint 8]

/-- The value an `ExecutionPayloadHeader` denotes. -/
def ExecutionPayloadHeader.toValue (e : ExecutionPayloadHeader) : Value :=
  .seq [.bytes e.parentHash.data, .bytes e.feeRecipient.data, .bytes e.stateRoot.data,
    .bytes e.receiptsRoot.data, .bytes e.logsBloom.data, .bytes e.prevRandao.data,
    .uint e.blockNumber, .uint e.gasLimit, .uint e.gasUsed, .uint e.timestamp,
    .bytes e.extraData.data, .uint e.baseFeePerGas, .bytes e.blockHash.data,
    .bytes e.transactionsRoot.data, .bytes e.withdrawalsRoot.data, .uint e.blobGasUsed,
    .uint e.excessBlobGas]

/-- An `ExecutionPayloadHeader` that fits its type. -/
structure ExecutionPayloadHeader.Fits (e : ExecutionPayloadHeader) : Prop where
  parentHash : e.parentHash.size = 32
  feeRecipient : e.feeRecipient.size = 20
  stateRoot : e.stateRoot.size = 32
  receiptsRoot : e.receiptsRoot.size = 32
  logsBloom : e.logsBloom.size = 256
  prevRandao : e.prevRandao.size = 32
  blockNumber : e.blockNumber < 2 ^ 64
  gasLimit : e.gasLimit < 2 ^ 64
  gasUsed : e.gasUsed < 2 ^ 64
  timestamp : e.timestamp < 2 ^ 64
  extraData : e.extraData.size ≤ 32
  baseFeePerGas : e.baseFeePerGas < 2 ^ 256
  blockHash : e.blockHash.size = 32
  transactionsRoot : e.transactionsRoot.size = 32
  withdrawalsRoot : e.withdrawalsRoot.size = 32
  blobGasUsed : e.blobGasUsed < 2 ^ 64
  excessBlobGas : e.excessBlobGas < 2 ^ 64

theorem htr_extraData (d : ByteArray) (hd : d.size ≤ 32) :
    hashTreeRoot (.byteList 32) (.bytes d.data) = .ok (mixInLength (bytesRoot d 0) d.size).data := by
  rw [htr_byteList 32 d.data (by simpa using hd), show _root_.Ssz.chunksForBytes 32 = 1 from rfl,
    show depthFor 1 = 0 by simp [depthFor], mixInLength, hash64_data, bytesRoot,
    subtree_data _ 0 (by decide), pack_data, leBytes_data]
  simp [mixIn, lengthWord]

/-- `ExecutionPayloadHeader.root` is `hash_tree_root`. -/
theorem ExecutionPayloadHeader.root_eq (e : ExecutionPayloadHeader) (hf : e.Fits) :
    hashTreeRoot executionPayloadHeaderDesc e.toValue = .ok e.root.data := by
  rw [executionPayloadHeaderDesc, toValue, htr_container _ _ _
    [e.parentHash.data, (bytesRoot e.feeRecipient 0).data, e.stateRoot.data, e.receiptsRoot.data,
      (bytesRoot e.logsBloom 3).data, e.prevRandao.data, (u64Root e.blockNumber).data,
      (u64Root e.gasLimit).data, (u64Root e.gasUsed).data, (u64Root e.timestamp).data,
      (mixInLength (bytesRoot e.extraData 0) e.extraData.size).data, (u256Root e.baseFeePerGas).data,
      e.blockHash.data, e.transactionsRoot.data, e.withdrawalsRoot.data,
      (u64Root e.blobGasUsed).data, (u64Root e.excessBlobGas).data] rfl (by
        simp only [List.zip, List.zipWith, List.mapM_cons, List.mapM_nil,
          htr_root32 _ hf.parentHash, htr_bytes e.feeRecipient 20 0 hf.feeRecipient
            (by simp [depthFor]) (by decide), htr_root32 _ hf.stateRoot, htr_root32 _ hf.receiptsRoot,
          htr_bytes e.logsBloom 256 3 hf.logsBloom (by simp [depthFor]) (by decide),
          htr_root32 _ hf.prevRandao, htr_u64 _ hf.blockNumber, htr_u64 _ hf.gasLimit,
          htr_u64 _ hf.gasUsed, htr_u64 _ hf.timestamp, htr_extraData _ hf.extraData,
          htr_u256 _ hf.baseFeePerGas, htr_root32 _ hf.blockHash, htr_root32 _ hf.transactionsRoot,
          htr_root32 _ hf.withdrawalsRoot, htr_u64 _ hf.blobGasUsed, htr_u64 _ hf.excessBlobGas]
        rfl) (by simp)]
  simp only [root, subtree_data _ 5 (by decide)]
  simp [nodes, depthFor]

/-! ### Electra and Fulu -/

/-- Electra's `LightClientHeader`. -/
def electraHeaderDesc : Desc :=
  .container ["beacon", "execution", "execution_branch"]
    [beaconBlockHeaderDesc, executionPayloadHeaderDesc, branchDesc Electra.executionBranchLength]

/-- The value an Electra `LightClientHeader` denotes. -/
def Electra.Header.toValue (h : Electra.Header) : Value :=
  .seq [h.beacon.toValue, h.execution.toValue, branchValue h.executionBranch]

/-- An Electra `LightClientHeader` that fits its type. -/
structure Electra.Header.Fits (h : Electra.Header) : Prop where
  beacon : h.beacon.Fits
  execution : h.execution.Fits
  executionBranch : BranchFits h.executionBranch Electra.executionBranchLength

/-- `Electra.Header.root` is `hash_tree_root`. -/
theorem Electra.Header.root_eq (h : Electra.Header) (hf : h.Fits) :
    hashTreeRoot electraHeaderDesc h.toValue = .ok h.root.data := by
  rw [electraHeaderDesc, toValue, htr_container _ _ _
    [h.beacon.root.data, h.execution.root.data, (branchRoot h.executionBranch 2).data] rfl (by
      simp only [List.zip, List.zipWith, List.mapM_cons, List.mapM_nil,
        BeaconBlockHeader.root_eq _ hf.beacon, ExecutionPayloadHeader.root_eq _ hf.execution,
        htr_branch _ _ 2 hf.executionBranch (by simp [Electra.executionBranchLength, depthFor])
          (by decide)]
      rfl) (by simp)]
  simp only [root, subtree_data _ 2 (by decide)]
  simp [nodes, depthFor]

/-- An Electra `LightClientBootstrap`. -/
def electraBootstrapDesc : Desc :=
  .container ["header", "current_sync_committee", "current_sync_committee_branch"]
    [electraHeaderDesc, syncCommitteeDesc, branchDesc Electra.syncCommitteeBranchLength]

/-- The value an Electra `LightClientBootstrap` denotes. -/
def Electra.Bootstrap.toValue (b : Electra.Bootstrap) : Value :=
  .seq [b.header.toValue, b.currentSyncCommittee.toValue, branchValue b.currentSyncCommitteeBranch]

/-- An Electra `LightClientBootstrap` that fits its type. -/
structure Electra.Bootstrap.Fits (b : Electra.Bootstrap) : Prop where
  header : b.header.Fits
  committee : b.currentSyncCommittee.Fits
  branch : BranchFits b.currentSyncCommitteeBranch Electra.syncCommitteeBranchLength

theorem Electra.Bootstrap.root_eq (b : Electra.Bootstrap) (hf : b.Fits) :
    hashTreeRoot electraBootstrapDesc b.toValue = .ok b.root.data := by
  rw [electraBootstrapDesc, toValue, htr_container _ _ _
    [b.header.root.data, b.currentSyncCommittee.root.data,
      (branchRoot b.currentSyncCommitteeBranch 3).data] rfl (by
      simp only [List.zip, List.zipWith, List.mapM_cons, List.mapM_nil,
        Electra.Header.root_eq _ hf.header, SyncCommittee.root_eq _ hf.committee,
        htr_branch _ _ 3 hf.branch (by simp [Electra.syncCommitteeBranchLength, depthFor])
          (by decide)]
      rfl) (by simp)]
  simp only [root, subtree_data _ 2 (by decide)]
  simp [nodes, depthFor]

/-- An Electra `LightClientUpdate`. -/
def electraUpdateDesc : Desc :=
  .container ["attested_header", "next_sync_committee", "next_sync_committee_branch",
      "finalized_header", "finality_branch", "sync_aggregate", "signature_slot"]
    [electraHeaderDesc, syncCommitteeDesc, branchDesc Electra.syncCommitteeBranchLength,
      electraHeaderDesc, branchDesc Electra.finalityBranchLength, syncAggregateDesc, .uint 8]

/-- The value an Electra `LightClientUpdate` denotes. -/
def Electra.Update.toValue (u : Electra.Update) : Value :=
  .seq [u.attestedHeader.toValue, u.nextSyncCommittee.toValue,
    branchValue u.nextSyncCommitteeBranch, u.finalizedHeader.toValue, branchValue u.finalityBranch,
    u.syncAggregate.toValue, .uint u.signatureSlot]

/-- An Electra `LightClientUpdate` that fits its type. -/
structure Electra.Update.Fits (u : Electra.Update) : Prop where
  attested : u.attestedHeader.Fits
  committee : u.nextSyncCommittee.Fits
  committeeBranch : BranchFits u.nextSyncCommitteeBranch Electra.syncCommitteeBranchLength
  finalized : u.finalizedHeader.Fits
  finalityBranch : BranchFits u.finalityBranch Electra.finalityBranchLength
  aggregate : u.syncAggregate.Fits
  signatureSlot : u.signatureSlot < 2 ^ 64

theorem Electra.Update.root_eq (u : Electra.Update) (hf : u.Fits) :
    hashTreeRoot electraUpdateDesc u.toValue = .ok u.root.data := by
  rw [electraUpdateDesc, toValue, htr_container _ _ _
    [u.attestedHeader.root.data, u.nextSyncCommittee.root.data,
      (branchRoot u.nextSyncCommitteeBranch 3).data, u.finalizedHeader.root.data,
      (branchRoot u.finalityBranch 3).data, u.syncAggregate.root.data,
      (u64Root u.signatureSlot).data] rfl (by
      simp only [List.zip, List.zipWith, List.mapM_cons, List.mapM_nil,
        Electra.Header.root_eq _ hf.attested, SyncCommittee.root_eq _ hf.committee,
        htr_branch _ _ 3 hf.committeeBranch (by simp [Electra.syncCommitteeBranchLength, depthFor])
          (by decide), Electra.Header.root_eq _ hf.finalized,
        htr_branch _ _ 3 hf.finalityBranch (by simp [Electra.finalityBranchLength, depthFor])
          (by decide), SyncAggregate.root_eq _ hf.aggregate, htr_u64 _ hf.signatureSlot]
      rfl) (by simp)]
  simp only [root, subtree_data _ 3 (by decide)]
  simp [nodes, depthFor]

/-- An Electra `LightClientFinalityUpdate`. -/
def electraFinalityUpdateDesc : Desc :=
  .container ["attested_header", "finalized_header", "finality_branch", "sync_aggregate",
      "signature_slot"]
    [electraHeaderDesc, electraHeaderDesc, branchDesc Electra.finalityBranchLength,
      syncAggregateDesc, .uint 8]

/-- The value an Electra `LightClientFinalityUpdate` denotes. -/
def Electra.FinalityUpdate.toValue (u : Electra.FinalityUpdate) : Value :=
  .seq [u.attestedHeader.toValue, u.finalizedHeader.toValue, branchValue u.finalityBranch,
    u.syncAggregate.toValue, .uint u.signatureSlot]

/-- An Electra `LightClientFinalityUpdate` that fits its type. -/
structure Electra.FinalityUpdate.Fits (u : Electra.FinalityUpdate) : Prop where
  attested : u.attestedHeader.Fits
  finalized : u.finalizedHeader.Fits
  finalityBranch : BranchFits u.finalityBranch Electra.finalityBranchLength
  aggregate : u.syncAggregate.Fits
  signatureSlot : u.signatureSlot < 2 ^ 64

theorem Electra.FinalityUpdate.root_eq (u : Electra.FinalityUpdate) (hf : u.Fits) :
    hashTreeRoot electraFinalityUpdateDesc u.toValue = .ok u.root.data := by
  rw [electraFinalityUpdateDesc, toValue, htr_container _ _ _
    [u.attestedHeader.root.data, u.finalizedHeader.root.data,
      (branchRoot u.finalityBranch 3).data, u.syncAggregate.root.data,
      (u64Root u.signatureSlot).data] rfl (by
      simp only [List.zip, List.zipWith, List.mapM_cons, List.mapM_nil,
        Electra.Header.root_eq _ hf.attested, Electra.Header.root_eq _ hf.finalized,
        htr_branch _ _ 3 hf.finalityBranch (by simp [Electra.finalityBranchLength, depthFor])
          (by decide), SyncAggregate.root_eq _ hf.aggregate, htr_u64 _ hf.signatureSlot]
      rfl) (by simp)]
  simp only [root, subtree_data _ 3 (by decide)]
  simp [nodes, depthFor]

/-- An Electra `LightClientOptimisticUpdate`. -/
def electraOptimisticUpdateDesc : Desc :=
  .container ["attested_header", "sync_aggregate", "signature_slot"]
    [electraHeaderDesc, syncAggregateDesc, .uint 8]

/-- The value an Electra `LightClientOptimisticUpdate` denotes. -/
def Electra.OptimisticUpdate.toValue (u : Electra.OptimisticUpdate) : Value :=
  .seq [u.attestedHeader.toValue, u.syncAggregate.toValue, .uint u.signatureSlot]

/-- An Electra `LightClientOptimisticUpdate` that fits its type. -/
structure Electra.OptimisticUpdate.Fits (u : Electra.OptimisticUpdate) : Prop where
  attested : u.attestedHeader.Fits
  aggregate : u.syncAggregate.Fits
  signatureSlot : u.signatureSlot < 2 ^ 64

theorem Electra.OptimisticUpdate.root_eq (u : Electra.OptimisticUpdate) (hf : u.Fits) :
    hashTreeRoot electraOptimisticUpdateDesc u.toValue = .ok u.root.data := by
  rw [electraOptimisticUpdateDesc, toValue, htr_container _ _ _
    [u.attestedHeader.root.data, u.syncAggregate.root.data, (u64Root u.signatureSlot).data] rfl (by
      simp only [List.zip, List.zipWith, List.mapM_cons, List.mapM_nil,
        Electra.Header.root_eq _ hf.attested, SyncAggregate.root_eq _ hf.aggregate,
        htr_u64 _ hf.signatureSlot]
      rfl) (by simp)]
  simp only [root, subtree_data _ 2 (by decide)]
  simp [nodes, depthFor]

/-! ### Gloas -/

/-- Gloas's `LightClientHeader`. -/
def gloasHeaderDesc : Desc :=
  .container ["beacon", "execution_block_hash", "execution_branch"]
    [beaconBlockHeaderDesc, bytes32, branchDesc Gloas.executionBranchLength]

/-- The value a Gloas `LightClientHeader` denotes. -/
def Gloas.Header.toValue (h : Gloas.Header) : Value :=
  .seq [h.beacon.toValue, .bytes h.executionBlockHash.data, branchValue h.executionBranch]

/-- A Gloas `LightClientHeader` that fits its type. -/
structure Gloas.Header.Fits (h : Gloas.Header) : Prop where
  beacon : h.beacon.Fits
  executionBlockHash : h.executionBlockHash.size = 32
  executionBranch : BranchFits h.executionBranch Gloas.executionBranchLength

theorem Gloas.Header.root_eq (h : Gloas.Header) (hf : h.Fits) :
    hashTreeRoot gloasHeaderDesc h.toValue = .ok h.root.data := by
  rw [gloasHeaderDesc, toValue, htr_container _ _ _
    [h.beacon.root.data, h.executionBlockHash.data, (branchRoot h.executionBranch 4).data] rfl (by
      simp only [List.zip, List.zipWith, List.mapM_cons, List.mapM_nil,
        BeaconBlockHeader.root_eq _ hf.beacon, htr_root32 _ hf.executionBlockHash,
        htr_branch _ _ 4 hf.executionBranch (by simp [Gloas.executionBranchLength, depthFor])
          (by decide)]
      rfl) (by simp)]
  simp only [root, subtree_data _ 2 (by decide)]
  simp [nodes, depthFor]

/-- A Gloas `LightClientBootstrap`. -/
def gloasBootstrapDesc : Desc :=
  .container ["header", "current_sync_committee", "current_sync_committee_branch"]
    [gloasHeaderDesc, syncCommitteeDesc, branchDesc Gloas.syncCommitteeBranchLength]

/-- The value a Gloas `LightClientBootstrap` denotes. -/
def Gloas.Bootstrap.toValue (b : Gloas.Bootstrap) : Value :=
  .seq [b.header.toValue, b.currentSyncCommittee.toValue, branchValue b.currentSyncCommitteeBranch]

/-- A Gloas `LightClientBootstrap` that fits its type. -/
structure Gloas.Bootstrap.Fits (b : Gloas.Bootstrap) : Prop where
  header : b.header.Fits
  committee : b.currentSyncCommittee.Fits
  branch : BranchFits b.currentSyncCommitteeBranch Gloas.syncCommitteeBranchLength

theorem Gloas.Bootstrap.root_eq (b : Gloas.Bootstrap) (hf : b.Fits) :
    hashTreeRoot gloasBootstrapDesc b.toValue = .ok b.root.data := by
  rw [gloasBootstrapDesc, toValue, htr_container _ _ _
    [b.header.root.data, b.currentSyncCommittee.root.data,
      (branchRoot b.currentSyncCommitteeBranch 4).data] rfl (by
      simp only [List.zip, List.zipWith, List.mapM_cons, List.mapM_nil,
        Gloas.Header.root_eq _ hf.header, SyncCommittee.root_eq _ hf.committee,
        htr_branch _ _ 4 hf.branch (by simp [Gloas.syncCommitteeBranchLength, depthFor])
          (by decide)]
      rfl) (by simp)]
  simp only [root, subtree_data _ 2 (by decide)]
  simp [nodes, depthFor]

/-- A Gloas `LightClientUpdate`. -/
def gloasUpdateDesc : Desc :=
  .container ["attested_header", "next_sync_committee", "next_sync_committee_branch",
      "finalized_header", "finality_branch", "sync_aggregate", "signature_slot"]
    [gloasHeaderDesc, syncCommitteeDesc, branchDesc Gloas.syncCommitteeBranchLength,
      gloasHeaderDesc, branchDesc Gloas.finalityBranchLength, syncAggregateDesc, .uint 8]

/-- The value a Gloas `LightClientUpdate` denotes. -/
def Gloas.Update.toValue (u : Gloas.Update) : Value :=
  .seq [u.attestedHeader.toValue, u.nextSyncCommittee.toValue,
    branchValue u.nextSyncCommitteeBranch, u.finalizedHeader.toValue, branchValue u.finalityBranch,
    u.syncAggregate.toValue, .uint u.signatureSlot]

/-- A Gloas `LightClientUpdate` that fits its type. -/
structure Gloas.Update.Fits (u : Gloas.Update) : Prop where
  attested : u.attestedHeader.Fits
  committee : u.nextSyncCommittee.Fits
  committeeBranch : BranchFits u.nextSyncCommitteeBranch Gloas.syncCommitteeBranchLength
  finalized : u.finalizedHeader.Fits
  finalityBranch : BranchFits u.finalityBranch Gloas.finalityBranchLength
  aggregate : u.syncAggregate.Fits
  signatureSlot : u.signatureSlot < 2 ^ 64

theorem Gloas.Update.root_eq (u : Gloas.Update) (hf : u.Fits) :
    hashTreeRoot gloasUpdateDesc u.toValue = .ok u.root.data := by
  rw [gloasUpdateDesc, toValue, htr_container _ _ _
    [u.attestedHeader.root.data, u.nextSyncCommittee.root.data,
      (branchRoot u.nextSyncCommitteeBranch 4).data, u.finalizedHeader.root.data,
      (branchRoot u.finalityBranch 4).data, u.syncAggregate.root.data,
      (u64Root u.signatureSlot).data] rfl (by
      simp only [List.zip, List.zipWith, List.mapM_cons, List.mapM_nil,
        Gloas.Header.root_eq _ hf.attested, SyncCommittee.root_eq _ hf.committee,
        htr_branch _ _ 4 hf.committeeBranch (by simp [Gloas.syncCommitteeBranchLength, depthFor])
          (by decide), Gloas.Header.root_eq _ hf.finalized,
        htr_branch _ _ 4 hf.finalityBranch (by simp [Gloas.finalityBranchLength, depthFor])
          (by decide), SyncAggregate.root_eq _ hf.aggregate, htr_u64 _ hf.signatureSlot]
      rfl) (by simp)]
  simp only [root, subtree_data _ 3 (by decide)]
  simp [nodes, depthFor]

/-- A Gloas `LightClientFinalityUpdate`. -/
def gloasFinalityUpdateDesc : Desc :=
  .container ["attested_header", "finalized_header", "finality_branch", "sync_aggregate",
      "signature_slot"]
    [gloasHeaderDesc, gloasHeaderDesc, branchDesc Gloas.finalityBranchLength, syncAggregateDesc,
      .uint 8]

/-- The value a Gloas `LightClientFinalityUpdate` denotes. -/
def Gloas.FinalityUpdate.toValue (u : Gloas.FinalityUpdate) : Value :=
  .seq [u.attestedHeader.toValue, u.finalizedHeader.toValue, branchValue u.finalityBranch,
    u.syncAggregate.toValue, .uint u.signatureSlot]

/-- A Gloas `LightClientFinalityUpdate` that fits its type. -/
structure Gloas.FinalityUpdate.Fits (u : Gloas.FinalityUpdate) : Prop where
  attested : u.attestedHeader.Fits
  finalized : u.finalizedHeader.Fits
  finalityBranch : BranchFits u.finalityBranch Gloas.finalityBranchLength
  aggregate : u.syncAggregate.Fits
  signatureSlot : u.signatureSlot < 2 ^ 64

theorem Gloas.FinalityUpdate.root_eq (u : Gloas.FinalityUpdate) (hf : u.Fits) :
    hashTreeRoot gloasFinalityUpdateDesc u.toValue = .ok u.root.data := by
  rw [gloasFinalityUpdateDesc, toValue, htr_container _ _ _
    [u.attestedHeader.root.data, u.finalizedHeader.root.data,
      (branchRoot u.finalityBranch 4).data, u.syncAggregate.root.data,
      (u64Root u.signatureSlot).data] rfl (by
      simp only [List.zip, List.zipWith, List.mapM_cons, List.mapM_nil,
        Gloas.Header.root_eq _ hf.attested, Gloas.Header.root_eq _ hf.finalized,
        htr_branch _ _ 4 hf.finalityBranch (by simp [Gloas.finalityBranchLength, depthFor])
          (by decide), SyncAggregate.root_eq _ hf.aggregate, htr_u64 _ hf.signatureSlot]
      rfl) (by simp)]
  simp only [root, subtree_data _ 3 (by decide)]
  simp [nodes, depthFor]

/-- A Gloas `LightClientOptimisticUpdate`. -/
def gloasOptimisticUpdateDesc : Desc :=
  .container ["attested_header", "sync_aggregate", "signature_slot"]
    [gloasHeaderDesc, syncAggregateDesc, .uint 8]

/-- The value a Gloas `LightClientOptimisticUpdate` denotes. -/
def Gloas.OptimisticUpdate.toValue (u : Gloas.OptimisticUpdate) : Value :=
  .seq [u.attestedHeader.toValue, u.syncAggregate.toValue, .uint u.signatureSlot]

/-- A Gloas `LightClientOptimisticUpdate` that fits its type. -/
structure Gloas.OptimisticUpdate.Fits (u : Gloas.OptimisticUpdate) : Prop where
  attested : u.attestedHeader.Fits
  aggregate : u.syncAggregate.Fits
  signatureSlot : u.signatureSlot < 2 ^ 64

theorem Gloas.OptimisticUpdate.root_eq (u : Gloas.OptimisticUpdate) (hf : u.Fits) :
    hashTreeRoot gloasOptimisticUpdateDesc u.toValue = .ok u.root.data := by
  rw [gloasOptimisticUpdateDesc, toValue, htr_container _ _ _
    [u.attestedHeader.root.data, u.syncAggregate.root.data, (u64Root u.signatureSlot).data] rfl (by
      simp only [List.zip, List.zipWith, List.mapM_cons, List.mapM_nil,
        Gloas.Header.root_eq _ hf.attested, SyncAggregate.root_eq _ hf.aggregate,
        htr_u64 _ hf.signatureSlot]
      rfl) (by simp)]
  simp only [root, subtree_data _ 2 (by decide)]
  simp [nodes, depthFor]

end LeanLight.Lc.Ssz
