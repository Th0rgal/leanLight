import LeanLightCli.Client

/-!
# A recorded run (`leanlight record`), replayed offline

Reads a recording's files and replays it through `LeanLight.Driver` at the recorded clock, as a
live run does, with no network: the tests (`LeanLightTests.ClientMain`) check what it accepts and
refuses, the benchmark (`LeanLightTests.BenchMain`) times it.
-/

namespace LeanLightTests.Fixture

open LeanLight.Lc LeanLight.Cli

/-- A recording: its directory and `meta.txt`'s values. -/
structure Fixture where
  dir : System.FilePath
  info : List (String × String)

def Fixture.get (f : Fixture) (k : String) : String := ((f.info.find? (·.1 == k)).map (·.2)).getD ""

def Fixture.now (f : Fixture) : Nat := (f.get "now_ms").toNat!

def Fixture.chain (f : Fixture) : Forks.Chain :=
  if f.get "network" == "sepolia" then Forks.sepolia else Forks.mainnet

def Fixture.bytes (f : Fixture) (file : String) : IO ByteArray := IO.FS.readBinFile (f.dir / file)

def Fixture.hexOf (f : Fixture) (k : String) : ByteArray := (hexBytes (f.get k)).getD .empty

def Fixture.fork (f : Fixture) (k : String) : Codec.Tag :=
  .name ((forkOfName (f.get k)).getD .fulu)

def load (dir : System.FilePath) : IO Fixture := do
  let lines ← IO.FS.lines (dir / "meta.txt")
  let info := lines.toList.filterMap fun l =>
    match l.splitOn " " with
    | [k, v] => some (k, v)
    | _ => none
  return ⟨dir, info⟩

/-- The recorded objects: the bootstrap, the period updates' chunks, the finality and optimistic
updates. -/
structure Objects where
  bootstrap : ByteArray
  chunks : Array Ssz.Chunk
  finality : ByteArray
  optimistic : ByteArray

def objects (f : Fixture) : IO Objects := do
  let some chunks := Ssz.parseUpdates (← f.bytes "updates.ssz")
    | throw (IO.userError "updates.ssz: bad framing")
  return ⟨← f.bytes "bootstrap.ssz", chunks, ← f.bytes "finality.ssz", ← f.bytes "optimistic.ssz"⟩

/-- The replay of `o` at clock `now` from checkpoint `root`: the store, or none when the
bootstrap is refused; and each update's verdict, in order (none: it did not decode). -/
def replay (c : Forks.Chain) (root : ByteArray) (now : Nat) (f : Fixture) (o : Objects) :
    Option Store.Store × List (Option Store.Verdict) := Id.run do
  let some s0 := Driver.start c root now (f.fork "bootstrap_fork") o.bootstrap | return (none, [])
  let mut s := s0
  let mut vs := []
  for ch in o.chunks do
    let (s', v) := Driver.feed c s now .update (.digest ch.digest) ch.ssz
    s := s'; vs := vs ++ [v]
  for (k, bs, fk) in [(Codec.Kind.finality, o.finality, "finality_fork"),
      (.optimistic, o.optimistic, "optimistic_fork")] do
    let (s', v) := Driver.feed c s now k (f.fork fk) bs
    s := s'; vs := vs ++ [v]
  return (some s, vs)

/-- The anchored block's header, rebuilt from `block.json` as the client rebuilds it. -/
def headerRlp (f : Fixture) : IO ByteArray := do
  match Json.parse (← IO.FS.readFile (f.dir / "block.json")) with
  | .error e => throw (IO.userError s!"block.json: {e}")
  | .ok j =>
    match LeanLight.Cli.headerRlp j with
    | .ok b => pure b
    | .error e => throw (IO.userError s!"block.json: {e}")

/-- A recorded read: its query's words and its files. -/
structure Read where
  words : List String
  files : List String

def reads (f : Fixture) : IO (List Read) := do
  let ls ← IO.FS.lines (f.dir / "reads.txt")
  return ls.toList.filterMap fun l =>
    match l.splitOn "\t" with
    | q :: files => if q.isEmpty then none else some ⟨(q.splitOn " ").filter (· ≠ ""), files⟩
    | [] => none

/-- An `eth_getProof` answer's account proof nodes and each storage proof's key and nodes, as the
client joins them. -/
def proofParts (j : Json) : Except String (ByteArray × List (List UInt8 × ByteArray)) := do
  let nodes ← proofNodes (← j.getObjVal? "accountProof")
  let sp ← (← j.getObjVal? "storageProof").getArr?
  let slots ← sp.toList.mapM fun p => do
    let some k := hexBytes (← (← p.getObjVal? "key").getStr?) | throw "key: not hex"
    let key := (List.replicate (32 - k.size) (0 : UInt8)) ++ k.data.toList
    return (key, ← proofNodes (← p.getObjVal? "proof"))
  return (nodes, slots)

def readJson (f : Fixture) (file : String) : IO Json := do
  match Json.parse (← IO.FS.readFile (f.dir / file)) with
  | .ok j => pure j
  | .error e => throw (IO.userError s!"{file}: {e}")

end LeanLightTests.Fixture
