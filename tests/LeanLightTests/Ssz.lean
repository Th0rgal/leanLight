import LeanLight.Ssz.Containers
import LeanLight.Ssz.Frame
import LeanLight.Forks

/-!
# The light client's SSZ against consensus-specs' vectors

`lake exe leanlight-ssz-test` (from `tests`): every committed vector of `vectors/ssz`
(consensus-specs v1.7.0-beta.4, mainnet preset; see its README) is decoded by `LeanLight.Ssz`,
encoded again by this file's test-only encoders, and hashed; the decode must succeed, the bytes
must come back unchanged and the root must be the vector's. Then each is mutated and must be
refused: a byte more or less for a fixed-size container, an offset moved by one, an
`extra_data` past 32 bytes. Each `single_merkle_proof` branch must verify at the gindex
`LeanLight.Ssz` pins, under the root it climbs to, and stop verifying when any node, the gindex or a
leading zero root is changed. The `/updates` framing and the fork digests are checked too. This
is a test, outside the runtime libraries: nothing here runs in the wallet.
-/

open LeanLight.Lc.Ssz

/-! ## Test-only encoders -/

namespace LeanLight.Lc.Ssz

def cat (xs : Array ByteArray) : ByteArray := xs.foldl (· ++ ·) .empty

def BeaconBlockHeader.encode (h : BeaconBlockHeader) : ByteArray :=
  leBytes 8 h.slot ++ leBytes 8 h.proposerIndex ++ h.parentRoot ++ h.stateRoot ++ h.bodyRoot

def SyncCommittee.encode (c : SyncCommittee) : ByteArray := cat c.pubkeys ++ c.aggregatePubkey

def SyncAggregate.encode (a : SyncAggregate) : ByteArray := a.bits ++ a.signature

def ExecutionPayloadHeader.encode (e : ExecutionPayloadHeader) : ByteArray :=
  e.parentHash ++ e.feeRecipient ++ e.stateRoot ++ e.receiptsRoot ++ e.logsBloom ++ e.prevRandao ++
    leBytes 8 e.blockNumber ++ leBytes 8 e.gasLimit ++ leBytes 8 e.gasUsed ++
    leBytes 8 e.timestamp ++ leBytes 4 ExecutionPayloadHeader.fixedSize ++
    leBytes 32 e.baseFeePerGas ++ e.blockHash ++ e.transactionsRoot ++ e.withdrawalsRoot ++
    leBytes 8 e.blobGasUsed ++ leBytes 8 e.excessBlobGas ++ e.extraData

def Electra.Header.encode (h : Electra.Header) : ByteArray :=
  h.beacon.encode ++ leBytes 4 Electra.Header.fixedSize ++ cat h.executionBranch ++
    h.execution.encode

def Electra.Bootstrap.encode (b : Electra.Bootstrap) : ByteArray :=
  leBytes 4 Electra.Bootstrap.fixedSize ++ b.currentSyncCommittee.encode ++
    cat b.currentSyncCommitteeBranch ++ b.header.encode

def Electra.Update.encode (u : Electra.Update) : ByteArray :=
  let a := u.attestedHeader.encode
  leBytes 4 Electra.Update.fixedSize ++ u.nextSyncCommittee.encode ++ cat u.nextSyncCommitteeBranch ++
    leBytes 4 (Electra.Update.fixedSize + a.size) ++ cat u.finalityBranch ++
    u.syncAggregate.encode ++ leBytes 8 u.signatureSlot ++ a ++ u.finalizedHeader.encode

def Electra.FinalityUpdate.encode (u : Electra.FinalityUpdate) : ByteArray :=
  let a := u.attestedHeader.encode
  leBytes 4 Electra.FinalityUpdate.fixedSize ++ leBytes 4 (Electra.FinalityUpdate.fixedSize + a.size) ++
    cat u.finalityBranch ++ u.syncAggregate.encode ++ leBytes 8 u.signatureSlot ++ a ++
    u.finalizedHeader.encode

def Electra.OptimisticUpdate.encode (u : Electra.OptimisticUpdate) : ByteArray :=
  leBytes 4 Electra.OptimisticUpdate.fixedSize ++ u.syncAggregate.encode ++
    leBytes 8 u.signatureSlot ++ u.attestedHeader.encode

def Gloas.Header.encode (h : Gloas.Header) : ByteArray :=
  h.beacon.encode ++ h.executionBlockHash ++ cat h.executionBranch

def Gloas.Bootstrap.encode (b : Gloas.Bootstrap) : ByteArray :=
  b.header.encode ++ b.currentSyncCommittee.encode ++ cat b.currentSyncCommitteeBranch

def Gloas.Update.encode (u : Gloas.Update) : ByteArray :=
  u.attestedHeader.encode ++ u.nextSyncCommittee.encode ++ cat u.nextSyncCommitteeBranch ++
    u.finalizedHeader.encode ++ cat u.finalityBranch ++ u.syncAggregate.encode ++
    leBytes 8 u.signatureSlot

def Gloas.FinalityUpdate.encode (u : Gloas.FinalityUpdate) : ByteArray :=
  u.attestedHeader.encode ++ u.finalizedHeader.encode ++ cat u.finalityBranch ++
    u.syncAggregate.encode ++ leBytes 8 u.signatureSlot

def Gloas.OptimisticUpdate.encode (u : Gloas.OptimisticUpdate) : ByteArray :=
  u.attestedHeader.encode ++ u.syncAggregate.encode ++ leBytes 8 u.signatureSlot

end LeanLight.Lc.Ssz

open LeanLight.Lc.Ssz (cat)

/-! ## Harness -/

/-- A type under test: decode, encode, root, and where its offsets sit (none if fixed-size). -/
structure Codec where
  decode : ByteArray → Option (ByteArray × ByteArray)
  /-- Byte positions of 4-byte offsets in its fixed part, each of which must be exact. -/
  offsets : List Nat
  fixed : Bool

def codec {α : Type} (decode : ByteArray → Option α) (encode : α → ByteArray)
    (root : α → ByteArray) (offsets : List Nat) (fixed : Bool) : Codec :=
  { decode := fun bs => (decode bs).map fun v => (encode v, root v), offsets, fixed }

def codecs : List (String × String × Codec) :=
  [ ("electra", "BeaconBlockHeader", codec BeaconBlockHeader.decode (·.encode) (·.root) [] true),
    ("gloas", "BeaconBlockHeader", codec BeaconBlockHeader.decode (·.encode) (·.root) [] true),
    ("electra", "SyncCommittee", codec SyncCommittee.decode (·.encode) (·.root) [] true),
    ("electra", "SyncAggregate", codec SyncAggregate.decode (·.encode) (·.root) [] true),
    ("electra", "ExecutionPayloadHeader",
      codec ExecutionPayloadHeader.decode (·.encode) (·.root) [436] false),
    ("fulu", "ExecutionPayloadHeader",
      codec ExecutionPayloadHeader.decode (·.encode) (·.root) [436] false) ] ++
  (["electra", "fulu"].flatMap fun f =>
    [ (f, "LightClientHeader", codec Electra.Header.decode (·.encode) (·.root) [112] false),
      (f, "LightClientBootstrap", codec Electra.Bootstrap.decode (·.encode) (·.root) [0] false),
      (f, "LightClientUpdate", codec Electra.Update.decode (·.encode) (·.root) [0] false),
      (f, "LightClientFinalityUpdate",
        codec Electra.FinalityUpdate.decode (·.encode) (·.root) [0] false),
      (f, "LightClientOptimisticUpdate",
        codec Electra.OptimisticUpdate.decode (·.encode) (·.root) [0] false) ]) ++
  [ ("gloas", "LightClientHeader", codec Gloas.Header.decode (·.encode) (·.root) [] true),
    ("gloas", "LightClientBootstrap", codec Gloas.Bootstrap.decode (·.encode) (·.root) [] true),
    ("gloas", "LightClientUpdate", codec Gloas.Update.decode (·.encode) (·.root) [] true),
    ("gloas", "LightClientFinalityUpdate",
      codec Gloas.FinalityUpdate.decode (·.encode) (·.root) [] true),
    ("gloas", "LightClientOptimisticUpdate",
      codec Gloas.OptimisticUpdate.decode (·.encode) (·.root) [] true) ]

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def hex (b : ByteArray) : String :=
  b.foldl (fun s x => s.push (hexDigit (x.toNat / 16)) |>.push (hexDigit (x.toNat % 16))) ""

def unhex (s : String) : ByteArray :=
  let ds := s.trimAscii.toString.toList.map fun c =>
    if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87
  let rec go : List Nat → Array UInt8 → Array UInt8
    | a :: b :: rest, acc => go rest (acc.push (16 * a + b).toUInt8)
    | _, acc => acc
  ⟨go ds #[]⟩

/-- `bs` with the 4-byte little-endian offset at `at` moved by `delta`. -/
def moveOffset (bs : ByteArray) (at_ : Nat) (delta : Int) : ByteArray :=
  let v := (Int.ofNat (readLE bs at_ 4) + delta).toNat
  let w := leBytes 4 v
  (List.range 4).foldl (fun b i => b.set! (at_ + i) (w.get! i)) bs

structure Tally where
  passed : Nat := 0
  failures : Array String := #[]

def Tally.check (t : Tally) (ok : Bool) (what : String) : Tally :=
  if ok then { t with passed := t.passed + 1 } else { t with failures := t.failures.push what }

def checkStatic (t : Tally) (dir : System.FilePath) (name : String) (c : Codec) : IO Tally := do
  let bs ← IO.FS.readBinFile (dir / "serialized.ssz")
  let want := (← IO.FS.readFile (dir / "root")).trimAscii.toString
  let mut t := t
  match c.decode bs with
  | none => t := t.check false s!"{dir}: {name} refused"
  | some (again, root) =>
    t := t.check (again == bs) s!"{dir}: {name} encodes back differently"
    t := t.check (hex root == want) s!"{dir}: {name} root {hex root}, expected {want}"
  -- Mutations that every decoder must refuse.
  if c.fixed then
    t := t.check (c.decode (bs.push 0)).isNone s!"{dir}: {name} accepted a byte more"
    t := t.check (c.decode (bs.extract 0 (bs.size - 1))).isNone s!"{dir}: {name} accepted a byte less"
  for o in c.offsets do
    for d in [(1 : Int), -1, 4] do
      t := t.check (c.decode (moveOffset bs o d)).isNone
        s!"{dir}: {name} accepted its offset at {o} moved by {d}"
  if !c.fixed then
    -- A last `extra_data` grown past 32 bytes.
    t := t.check (c.decode (bs ++ ⟨Array.replicate 33 7⟩)).isNone
      s!"{dir}: {name} accepted 33 more bytes of extra_data"
  return t

/-- `(fork, kind, proof name) ↦ the gindex LeanLight.Ssz pins`. -/
def gindexFor : String → String → Option Nat
  | "electra", "current_sync_committee_merkle_proof" => some gindexCurrentSyncCommitteeElectra
  | "electra", "next_sync_committee_merkle_proof" => some gindexNextSyncCommitteeElectra
  | "electra", "finality_root_merkle_proof" => some gindexFinalizedRootElectra
  | "electra", "execution_merkle_proof" => some gindexExecutionPayload
  | "fulu", "current_sync_committee_merkle_proof" => some gindexCurrentSyncCommitteeElectra
  | "fulu", "next_sync_committee_merkle_proof" => some gindexNextSyncCommitteeElectra
  | "fulu", "finality_root_merkle_proof" => some gindexFinalizedRootElectra
  | "fulu", "execution_merkle_proof" => some gindexExecutionPayload
  | "gloas", "current_sync_committee_merkle_proof" => some gindexCurrentSyncCommitteeGloas
  | "gloas", "next_sync_committee_merkle_proof" => some gindexNextSyncCommitteeGloas
  | "gloas", "finality_root_merkle_proof" => some gindexFinalizedRootGloas
  | "gloas", "execution_block_hash_merkle_proof" => some gindexExecutionBlockHashGloas
  | _, _ => none

def flipByte (b : ByteArray) : ByteArray := b.set! 0 (b.get! 0 ^^^ 1)

def checkBranch (t : Tally) (dir : System.FilePath) (fork name : String) : IO Tally := do
  let lines := (← IO.FS.readFile (dir / "proof")).splitOn "\n" |>.filter (· ≠ "")
  let leaf := unhex (lines[0]?.getD "")
  let index := (lines[1]?.getD "").toNat!
  let branch := (lines.drop 2).toArray.map unhex
  let mut t := t
  t := t.check (gindexFor fork name == some index) s!"{dir}: leaf_index {index} is not the pinned gindex"
  t := t.check (branch.size == index.log2) s!"{dir}: branch of {branch.size}, depth {index.log2}"
  -- The root the branch climbs to; the object's root (recorded where it was recomputed) must be it.
  let root := climb index branch 0 index.log2 0 leaf
  if ← (dir / "object.root").pathExists then
    let want := (← IO.FS.readFile (dir / "object.root")).trimAscii.toString
    t := t.check (hex root == want) s!"{dir}: branch climbs to {hex root}, object root {want}"
  t := t.check (isValidNormalizedBranch leaf branch index root) s!"{dir}: branch refused"
  -- Normalized: a leading zero root is accepted, a leading non-zero one refused.
  t := t.check (isValidNormalizedBranch leaf (#[zeroChunk] ++ branch) index root)
    s!"{dir}: a leading zero root refused"
  t := t.check (!(isValidNormalizedBranch leaf (#[flipByte zeroChunk] ++ branch) index root))
    s!"{dir}: a leading non-zero root accepted"
  t := t.check (!(isValidNormalizedBranch leaf (branch.pop) index root)) s!"{dir}: a short branch accepted"
  t := t.check (!(isValidNormalizedBranch (flipByte leaf) branch index root)) s!"{dir}: another leaf accepted"
  -- The sibling's gindex swaps the sides at the leaf: the same root exactly when the leaf and
  -- its sibling are equal (two equal committees, or a zero finalized checkpoint, in these states).
  let same := leaf.data == (branch[0]?.getD ByteArray.empty).data
  t := t.check (isValidNormalizedBranch leaf branch (index ^^^ 1) root == same)
    s!"{dir}: the sibling gindex judged wrongly"
  t := t.check (!(isValidNormalizedBranch leaf branch (2 * index) root)) s!"{dir}: a deeper gindex accepted"
  for i in [0:branch.size] do
    t := t.check (!(isValidNormalizedBranch leaf (branch.modify i flipByte) index root))
      s!"{dir}: branch node {i} altered, accepted"
  return t

/-! ## Framing and digests -/

def checkFrames (t : Tally) : Tally := Id.run do
  let c₁ : Chunk := { digest := ⟨#[1, 2, 3, 4]⟩, ssz := ⟨Array.replicate 26424 9⟩ }
  let c₂ : Chunk := { digest := ⟨#[5, 6, 7, 8]⟩, ssz := ⟨Array.replicate 10 1⟩ }
  let bs := encodeUpdates [c₁, c₂]
  let mut t := t
  t := t.check (readLE bs 0 8 == 26428) "the first chunk's length is not 4 + 26424"
  t := t.check (match parseUpdates bs with
    | some cs => cs.size == 2 &&
        (cs.map (fun c => (c.digest.data, c.ssz.data))) ==
          #[(c₁.digest.data, c₁.ssz.data), (c₂.digest.data, c₂.ssz.data)]
    | none => false) "two chunks not parsed back"
  t := t.check ((parseUpdates .empty).map (·.size) == some 0) "an empty answer refused"
  t := t.check (parseUpdates (bs.push 0)).isNone "a trailing byte accepted"
  t := t.check (parseUpdates (bs.extract 0 (bs.size - 1))).isNone "a truncated chunk accepted"
  -- A length that does not count the digest: the chunk runs 4 bytes short, the rest misparses.
  let short := (leBytes 8 c₂.ssz.size ++ c₂.digest ++ c₂.ssz)
  t := t.check (parseUpdates short).isNone "a length without the digest accepted"
  t := t.check (parseUpdates (leBytes 8 3 ++ ⟨#[1, 2, 3]⟩)).isNone "a length below 4 accepted"
  let many := encodeUpdates (List.replicate 129 c₂)
  t := t.check (parseUpdates many).isNone "129 chunks accepted"
  t := t.check ((parseUpdates (encodeUpdates (List.replicate 128 c₂))).map (·.size) == some 128)
    "128 chunks refused"
  return t

/-- facts.md's digests (2026-10-24), each at its fork's or BPO's first epoch. -/
def digestCases : List (String × ForkTable × Nat × String) :=
  let mainnet := LeanLight.Lc.Forks.mainnet.forkTable
  let sepolia := LeanLight.Lc.Forks.sepolia.forkTable
  [ ("mainnet electra", mainnet, 364032, "ad532ceb"), ("mainnet fulu", mainnet, 411392, "cc2c5cdb"),
    ("mainnet bpo1", mainnet, 412672, "cb0d1acc"), ("mainnet bpo2", mainnet, 419072, "8c9f62fe"),
    ("mainnet bpo2 later", mainnet, 500000, "8c9f62fe"),
    ("sepolia electra", sepolia, 222464, "14045b5a"), ("sepolia fulu", sepolia, 272640, "7e0d3447"),
    ("sepolia bpo1", sepolia, 274176, "fd32b622"), ("sepolia bpo2", sepolia, 275712, "74d01459"),
    ("sepolia gloas", sepolia, 353024, "669e6c11"), ("sepolia gloas later", sepolia, 360000, "669e6c11") ]

def checkDigests (t : Tally) : Tally := Id.run do
  let mainnet := LeanLight.Lc.Forks.mainnet.forkTable
  let mut t := t
  for (name, table, epoch, want) in digestCases do
    let got := (table.digest epoch).map hex
    t := t.check (got == some want) s!"{name}: digest {got}, expected {want}"
  t := t.check (mainnet.digest 364031).isNone "mainnet: a digest before Electra"
  -- Known pre-Electra digests from the fork data root alone (facts.md): mainnet phase0 and Deneb.
  t := t.check (hex (LeanLight.Lc.Bytes.extract (forkDataRoot ⟨#[0, 0, 0, 0]⟩ mainnet.genesisValidatorsRoot) 0 4)
    == "b5303f2a") "mainnet phase0 digest"
  t := t.check (hex (LeanLight.Lc.Bytes.extract (forkDataRoot ⟨#[4, 0, 0, 0]⟩ mainnet.genesisValidatorsRoot) 0 4)
    == "6a95a1a9") "mainnet deneb digest"
  return t

/-! ## SHA-256 -/

/-- NIST's examples (FIPS 180-4 appendix / CSRC "SHA256.pdf") and padding boundaries
(55, 56, 63, 64, 119 bytes of 'a', hashed with Python's `hashlib`). -/
def shaCases : List (ByteArray × String) :=
  let a (n : Nat) : ByteArray := ⟨Array.replicate n 0x61⟩
  [ ("".toUTF8, "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
    ("abc".toUTF8, "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
    ("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8,
      "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"),
    (a 55, "9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318"),
    (a 56, "b35439a4ac6f0948b6d6f9e3c6af0f5f590ce20f1bde7090ef7970686ec6738a"),
    (a 63, "7d3e74a05d7db15bce4ad9ec0658ea98e3f06eeecf16b4c6fff2da457ddc2f34"),
    (a 64, "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb"),
    (a 119, "31eba51c313a5c08226adf18d4a359cfdfd8d2e816b13f4af952f7ea6584dcfb"),
    (a 1000000, "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0") ]

def checkSha (t : Tally) : Tally :=
  shaCases.foldl (fun t (m, want) =>
    t.check (hex (Ssz.Sha256.hash m) == want) s!"sha256 of {m.size} bytes") t

def main (args : List String) : IO UInt32 := do
  let root : System.FilePath := args.headD "vectors/ssz"
  let mut t : Tally := {}
  let mut cases := 0
  for (fork, name, c) in codecs do
    for case in ["case_0", "case_1"] do
      t ← checkStatic t (root / "ssz_static" / fork / name / case) name c
      cases := cases + 1
  let mut proofs := 0
  for fork in ["electra", "fulu", "gloas"] do
    for kind in ["BeaconState", "BeaconBlockBody"] do
      let dir := root / "single_merkle_proof" / fork / kind
      if ← dir.pathExists then
        for entry in ← dir.readDir do
          t ← checkBranch t entry.path fork entry.fileName
          proofs := proofs + 1
  t := checkFrames t
  t := checkDigests t
  t := checkSha t
  for f in t.failures do IO.eprintln s!"FAIL {f}"
  IO.println s!"leanlight-ssz-test: {cases} ssz_static cases, {proofs} single_merkle_proof cases, {t.passed} checks passed, {t.failures.size} failed"
  return if t.failures.isEmpty then 0 else 1
