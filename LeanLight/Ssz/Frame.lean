import LeanLight.Ssz.Merkle

/-!
# The `/updates` framing and fork digests

**Framing.** An SSZ answer to `GET /eth/v1/beacon/light_client/updates` (beacon-APIs `79b9b05`,
`updates.yaml:43-69`) is a run of chunks, each a little-endian `uint64` length, a 4-byte fork
digest, then the update's SSZ, and **the length counts the digest**: length = 4 + the SSZ's
length (leanKohakuDesktop's `spec/16-light-client.md`, "The beacon API"). `parseUpdates` reads at most
`maxRequestUpdates` (128, `MAX_REQUEST_LIGHT_CLIENT_UPDATES`) chunks and refuses the whole
answer on a length below 4, a chunk past the end, or bytes left over; `LeanLightProofs.SszFrame`
proves it inverse to `encodeUpdates`.

**Re-encoded chunks.** netd re-encodes a JSON answer to SSZ for a source that serves no SSZ
(open decision 1), and tags each item with a fork byte instead of a digest: `u64le(1 + |ssz|)`,
the fork (`0` Electra, `1` Fulu, `2` Gloas, the evidence's numbering), the SSZ (the channel's
`Updates` response of form `1`, leanKohakuDesktop's `spec/16-light-client.md`, "Frame layouts"). `parseForkUpdates`
reads at most 128 such chunks and refuses a length below 1, a fork byte above 2, a chunk past the
end, or bytes left over; `LeanLightProofs.SszFrame` proves it inverse to `encodeForkUpdates` both
ways.

**Fork digests.** `forkDigest` is consensus-specs' `compute_fork_digest(genesis_validators_root,
epoch)` as Fulu amends it (EIP-7892, `fulu/beacon-chain.md:322-344`): before
`FULU_FORK_EPOCH`, the first 4 bytes of the fork data root of the epoch's fork version; from
it on, those bytes XOR the first 4 of `sha256(u64le(e) ‖ u64le(m))`, where `(e, m)` is the
blob-parameter entry in force at the epoch, `(ELECTRA_FORK_EPOCH, MAX_BLOBS_PER_BLOCK_ELECTRA)`
before the first. A BPO entry changes the digest and not the fork version. The chains' tables
are `LeanLight.Forks`' (`Chain.forkTable`); the digests they give are checked against facts.md's
table by the vector tests.
-/

namespace LeanLight.Lc.Ssz

/-! ## Framing -/

/-- `MAX_REQUEST_LIGHT_CLIENT_UPDATES`. -/
def maxRequestUpdates : Nat := 128

/-- One chunk of an `/updates` answer. -/
structure Chunk where
  digest : ByteArray
  ssz : ByteArray

/-- A chunk's bytes: `u64le(4 + |ssz|) ‖ digest ‖ ssz`. -/
def Chunk.bytes (c : Chunk) : ByteArray := leBytes 8 (4 + c.ssz.size) ++ c.digest ++ c.ssz

/-- The chunks of `bs` from `off`, at most `fuel` more, appended to `acc` in order. -/
def parseChunks (bs : ByteArray) : Nat → Nat → Array Chunk → Option (Array Chunk)
  | fuel, off, acc =>
    if off = bs.size then some acc
    else
      match fuel with
      | 0 => none
      | fuel + 1 =>
        let len := readLE bs off 8
        if 4 ≤ len ∧ off + 8 + len ≤ bs.size then
          parseChunks bs fuel (off + 8 + len)
            (acc.push { digest := Bytes.extract bs (off + 8) (off + 12),
                        ssz := Bytes.extract bs (off + 12) (off + 8 + len) })
        else none

/-- The chunks of an `/updates` answer, at most 128, or `none` if it is not exactly a run of
them. -/
def parseUpdates (bs : ByteArray) : Option (Array Chunk) := parseChunks bs maxRequestUpdates 0 #[]

/-- The bytes of a run of chunks. -/
def encodeUpdates (cs : List Chunk) : ByteArray := cs.foldl (fun acc c => acc ++ c.bytes) .empty

/-- One chunk of a re-encoded `/updates` answer: the fork (`0` Electra, `1` Fulu, `2` Gloas)
and netd's SSZ of the item. -/
structure ForkChunk where
  fork : UInt8
  ssz : ByteArray

/-- A re-encoded chunk's bytes: `u64le(1 + |ssz|) ‖ fork ‖ ssz`. -/
def ForkChunk.bytes (c : ForkChunk) : ByteArray :=
  leBytes 8 (1 + c.ssz.size) ++ (ByteArray.empty.push c.fork) ++ c.ssz

/-- The re-encoded chunks of `bs` from `off`, at most `fuel` more, appended to `acc` in order. -/
def parseForkChunks (bs : ByteArray) : Nat → Nat → Array ForkChunk → Option (Array ForkChunk)
  | fuel, off, acc =>
    if off = bs.size then some acc
    else
      match fuel with
      | 0 => none
      | fuel + 1 =>
        let len := readLE bs off 8
        if 1 ≤ len ∧ off + 8 + len ≤ bs.size ∧ Bytes.byteAt bs (off + 8) ≤ 2 then
          parseForkChunks bs fuel (off + 8 + len)
            (acc.push { fork := Bytes.byteAt bs (off + 8),
                        ssz := Bytes.extract bs (off + 9) (off + 8 + len) })
        else none

/-- The chunks of a re-encoded `/updates` answer, at most 128, or `none` if it is not exactly a
run of them. -/
def parseForkUpdates (bs : ByteArray) : Option (Array ForkChunk) :=
  parseForkChunks bs maxRequestUpdates 0 #[]

/-- The bytes of a run of re-encoded chunks. -/
def encodeForkUpdates (cs : List ForkChunk) : ByteArray :=
  cs.foldl (fun acc c => acc ++ c.bytes) .empty

/-! ## Fork digests -/

/-- A fork version: 4 bytes. -/
abbrev Version := ByteArray

/-- The fork data root of a version and a genesis validators root: `hash_tree_root(ForkData)`,
two fields, the version padded to a node. -/
def forkDataRoot (version : Version) (gvr : ByteArray) : ByteArray :=
  hash64 (bytesRoot version 0) gvr

/-- A chain's fork schedule from Electra on, and its blob-parameter schedule. -/
structure ForkTable where
  genesisValidatorsRoot : ByteArray
  /-- `(epoch, version)` of each fork from Electra on, in increasing epoch order. -/
  forks : List (Nat × Version)
  fuluEpoch : Nat
  electraEpoch : Nat
  maxBlobsElectra : Nat
  /-- `BLOB_SCHEDULE`: `(epoch, max_blobs_per_block)`, in increasing epoch order. -/
  blobSchedule : List (Nat × Nat)

/-- The version of the last fork at or before `epoch` (`compute_fork_version`), if any. -/
def ForkTable.versionAt (t : ForkTable) (epoch : Nat) : Option Version :=
  (t.forks.filter (·.1 ≤ epoch)).getLast?.map (·.2)

/-- The blob parameters in force at `epoch` (`get_blob_parameters`). -/
def ForkTable.blobParametersAt (t : ForkTable) (epoch : Nat) : Nat × Nat :=
  (t.blobSchedule.filter (·.1 ≤ epoch)).getLast?.getD (t.electraEpoch, t.maxBlobsElectra)

/-- The first 4 bytes of `a XOR b`. -/
def xor4 (a b : ByteArray) : ByteArray :=
  ⟨#[a[0]?.getD 0 ^^^ b[0]?.getD 0, a[1]?.getD 0 ^^^ b[1]?.getD 0,
    a[2]?.getD 0 ^^^ b[2]?.getD 0, a[3]?.getD 0 ^^^ b[3]?.getD 0]⟩

/-- `compute_fork_digest(genesis_validators_root, epoch)`, BPO-aware; `none` before the table's
first fork. -/
def ForkTable.digest (t : ForkTable) (epoch : Nat) : Option ByteArray :=
  (t.versionAt epoch).map fun version =>
    let base := forkDataRoot version t.genesisValidatorsRoot
    if epoch < t.fuluEpoch then Bytes.extract base 0 4
    else
      let (e, m) := t.blobParametersAt epoch
      xor4 base (Ssz.Sha256.hash (leBytes 8 e ++ leBytes 8 m))

/-- Bytes from a list of byte values. -/
def bytesOf (l : List Nat) : ByteArray := ⟨(l.map UInt8.ofNat).toArray⟩

end LeanLight.Lc.Ssz
