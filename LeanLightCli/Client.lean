import LeanLight
import LeanLightCli.Util

/-!
# Sync and verified reads

The light client's loop, as Helios runs it, over `LeanLight`:

1. **Bootstrap** from a checkpoint root: `GET /eth/v1/beacon/light_client/bootstrap/{root}` (SSZ),
   decoded as the fork its `Eth-Consensus-Version` names (`Codec.decodeBootstrap`), then
   `Store.bootstrap` (the header's root is the checkpoint, the committee's branch, the age bound,
   every key validated).
2. **Updates**, period by period up to the clock's: `GET .../updates?start_period=p&count=n`
   (SSZ chunks tagged by fork digest, `Ssz.parseUpdates`), each through `Store.receive` (BLS
   signature of two thirds of the committee, branches, the sync protocol's rules).
3. **The finality and optimistic updates**, through `Store.receive` too.

The store's anchor is the newest attested header two thirds of the committee signed. A read is
answered at the execution block that header names: the block's header, rebuilt in RLP from
`eth_getBlockByHash`, must hash to the beacon header's execution block hash and match its fields
(`Anchor.bind`); an account and its storage are read from `eth_getProof`'s nodes under that
header's state root (`Facts.account`, `Facts.storage`), and code is accepted only when it hashes
to the proved code hash. The endpoint's own account fields are never read.
-/

namespace LeanLight.Cli

open LeanLight.Lc
open LeanLight.Lc.Forks (Chain ForkName)

def forkOfName : String → Option ForkName
  | "electra" => some .electra
  | "fulu" => some .fulu
  | "gloas" => some .gloas
  | _ => none

def verdictName : Store.Verdict → String
  | .halted => "halted"
  | .malformed => "malformed"
  | .unknownPeriod => "unknown period"
  | .tooOld => "too old"
  | .badSignature => "bad signature"
  | .conflict => "conflict"
  | .compared => "compared"
  | .irrelevant => "irrelevant"
  | .badKeys => "bad keys"
  | .accepted a l => s!"accepted (applied {a}, learned {l})"

structure Config where
  chain : Chain
  consensus : String
  execution : String
  checkpoint : Option ByteArray := none

/-- What a sync did. -/
structure Synced where
  store : Store.Store
  updates : Nat := 0
  accepted : Nat := 0
  refused : List String := []

def die {α} (msg : String) : IO α := throw (IO.userError msg)

def orDie {α} (what : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => die s!"{what}: {e}"

/-- The checkpoint: the one given, else the beacon node's finalized root (trust on first use, as
Helios does without a checkpoint). -/
def checkpointOf (cfg : Config) : IO ByteArray := do
  if let some c := cfg.checkpoint then return c
  let j ← orDie "finalized header" (← getJson s!"{cfg.consensus}/eth/v1/beacon/headers/finalized")
  let root ← orDie "finalized header" do (← (← j.getObjVal? "data").getObjVal? "root").getStr?
  match hexBytes root with
  | some r => IO.eprintln s!"checkpoint (the node's finalized root, unchecked): {root}"; return r
  | none => die "finalized header: bad root"

def bootstrap (cfg : Config) (root : ByteArray) : IO Store.Store := do
  let (bs, version) ← orDie "bootstrap"
    (← getSsz s!"{cfg.consensus}/eth/v1/beacon/light_client/bootstrap/{toHex root}")
  let some fork := version.bind forkOfName | die s!"bootstrap: fork {version} unknown"
  let now ← nowMs
  timeVerify do
    let some b := Codec.decodeBootstrap Codec.mainnet cfg.chain (.name fork) bs
      | die "bootstrap: does not decode as its fork's LightClientBootstrap"
    match Store.bootstrap cfg.chain root now b with
    | some s => pure s
    | none => die "bootstrap: refused (root, committee branch, age or keys)"

/-- One update through the store. -/
def receive (cfg : Config) (sy : Synced) (k : Codec.Kind) (tag : Codec.Tag) (bs : ByteArray) :
    IO Synced := do
  let now ← nowMs
  timeVerify do
    match Codec.decodeUpdate Codec.mainnet cfg.chain k tag bs with
    | none => pure { sy with updates := sy.updates + 1, refused := "undecodable" :: sy.refused }
    | some u =>
      let (s, v) := Store.receive cfg.chain sy.store now u
      log s!"  update attested {u.slot} signature {u.signatureSlot}: {verdictName v}"
      match v with
      | .accepted _ _ => pure { sy with store := s, updates := sy.updates + 1, accepted := sy.accepted + 1 }
      | .irrelevant | .compared => pure { sy with store := s, updates := sy.updates + 1 }
      | v => pure { sy with store := s, updates := sy.updates + 1, refused := verdictName v :: sy.refused }

def currentPeriod (c : Chain) : IO Nat := do
  return c.periodAt (c.slotOf (← nowMs))

/-- Bootstrap, then updates up to the clock's period, then the finality and optimistic updates. -/
def sync (cfg : Config) : IO Synced := do
  let root ← checkpointOf cfg
  let mut sy : Synced := { store := ← bootstrap cfg root }
  let cur ← currentPeriod cfg.chain
  let mut guard := 0
  while Store.period cfg.chain sy.store < cur || sy.store.next.isNone do
    guard := guard + 1
    if guard > 64 then break
    let p := Store.period cfg.chain sy.store
    let count := min 128 (cur - p + 1)
    let (bs, _) ← orDie "updates" (← getSsz
      s!"{cfg.consensus}/eth/v1/beacon/light_client/updates?start_period={p}&count={count}")
    let some chunks := Ssz.parseUpdates bs | die "updates: bad framing"
    let before := (Store.period cfg.chain sy.store, sy.store.next.isSome)
    for ch in chunks do
      sy ← receive cfg sy .update (.digest ch.digest) ch.ssz
    if (Store.period cfg.chain sy.store, sy.store.next.isSome) == before then break
  for (k, path) in [(Codec.Kind.finality, "finality_update"), (.optimistic, "optimistic_update")] do
    let (bs, version) ← orDie path (← getSsz s!"{cfg.consensus}/eth/v1/beacon/light_client/{path}")
    let some fork := version.bind forkOfName | die s!"{path}: fork {version} unknown"
    sy ← receive cfg sy k (.name fork) bs
  return sy

/-! ## Reads at the anchor -/

/-- The header's fields in their RLP order (London to Amsterdam), and whether each is a quantity. -/
def headerFields : List (String × Bool) :=
  [("parentHash", false), ("sha3Uncles", false), ("miner", false), ("stateRoot", false),
   ("transactionsRoot", false), ("receiptsRoot", false), ("logsBloom", false),
   ("difficulty", true), ("number", true), ("gasLimit", true), ("gasUsed", true),
   ("timestamp", true), ("extraData", false), ("mixHash", false), ("nonce", false),
   ("baseFeePerGas", true), ("withdrawalsRoot", false), ("blobGasUsed", true),
   ("excessBlobGas", true), ("parentBeaconBlockRoot", false), ("requestsHash", false),
   ("blockAccessListHash", false), ("slotNumber", true)]

/-- The RLP of a block's header, rebuilt from `eth_getBlockByHash`'s fields. Untrusted:
`Anchor.bind` checks it hashes to the anchored block hash. -/
def headerRlp (block : Lean.Json) : Except String ByteArray := do
  let mut payload : List UInt8 := []
  for (name, quantity) in headerFields do
    match block.getObjVal? name with
    | .error _ => break
    | .ok v =>
      let s ← v.getStr?
      let field ← if quantity then
          match hexNat s with
          | some n => pure (Spec.Rlp.be n)
          | none => throw s!"{name}: not a quantity"
        else
          match hexBytes s with
          | some b => pure b.data.toList
          | none => throw s!"{name}: not hex"
      match Spec.Rlp.encodeBytes field with
      | some e => payload := payload ++ e
      | none => throw s!"{name}: too long"
  match Spec.Rlp.encodeList payload with
  | some e => return ⟨e.toArray⟩
  | none => throw "header too long"

/-- An `eth_getProof` proof's nodes, joined as `Mpt.lookup` reads them: the first, then every
later node of at least 32 bytes (a shorter one is inline in its parent). -/
def proofNodes (items : Lean.Json) : Except String ByteArray := do
  let arr ← items.getArr?
  let mut out := ByteArray.empty
  let mut i := 0
  for it in arr do
    let some b := hexBytes (← it.getStr?) | throw "proof node: not hex"
    if i == 0 || b.size ≥ 32 then out := out ++ b
    i := i + 1
  return out

/-- The anchored block: its beacon header and the EL header's RLP, bound. -/
structure Anchored where
  beacon : Store.Header
  rlp : ByteArray
  el : Spec.Header.Header
  hash : ByteArray

def anchoredBlock (cfg : Config) (s : Store.Store) : IO Anchored := do
  let some a := Store.anchored cfg.chain s (← nowMs) | die "no anchor: the store is halted or too old"
  let hash := a.header.elHash
  let block ← orDie "eth_getBlockByHash"
    (← rpc cfg.execution "eth_getBlockByHash" (.arr #[toHex hash, false]))
  let rlp ← orDie "header" (headerRlp block)
  timeVerify do
    match Anchor.bind cfg.chain a.header rlp with
    | some h => pure { beacon := a.header, rlp, el := h, hash }
    | none => die "header: the endpoint's block does not match the anchored execution block"

/-- What a verified read says. -/
structure AccountRead where
  account : Spec.Mpt.Account
  slots : List Nat

def readAccount (cfg : Config) (b : Anchored) (addr : ByteArray) (slots : List ByteArray) :
    IO AccountRead := do
  let keys := slots.map fun k => toHex k
  let r ← orDie "eth_getProof" (← rpc cfg.execution "eth_getProof"
    (.arr #[toHex addr, .arr (keys.toArray.map Lean.Json.str), toHex b.hash]))
  let nodes ← orDie "accountProof" (proofNodes (← orDie "eth_getProof" (r.getObjVal? "accountProof")))
  let sp ← orDie "storageProof" do (← r.getObjVal? "storageProof").getArr?
  if sp.size != slots.length then die "eth_getProof: wrong number of storage proofs"
  let mut pairs : List (List UInt8 × ByteArray) := []
  for (k, p) in slots.zip sp.toList do
    let ns ← orDie "storage proof" do proofNodes (← p.getObjVal? "proof")
    pairs := pairs ++ [(k.data.toList, ns)]
  timeVerify do
    match Facts.storage cfg.chain b.beacon b.rlp addr.data.toList nodes pairs with
    | some (_, acct, vs) => pure { account := acct, slots := vs }
    | none => die "eth_getProof: the proof does not prove the account under the anchored state root"

/-- The code at `addr`, accepted only when it hashes to the proved code hash. -/
def readCode (cfg : Config) (b : Anchored) (addr : ByteArray) (codeHash : List UInt8) :
    IO ByteArray := do
  let r ← orDie "eth_getCode" (← rpc cfg.execution "eth_getCode" (.arr #[toHex addr, toHex b.hash]))
  let some code := hexBytes (← orDie "eth_getCode" r.getStr?) | die "eth_getCode: not hex"
  timeVerify do
    if Spec.Common.keccak code.data.toList == codeHash then pure code
    else die "eth_getCode: the code does not hash to the proved code hash"

end LeanLight.Cli
