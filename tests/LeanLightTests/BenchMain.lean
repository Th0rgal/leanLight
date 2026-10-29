import LeanLightTests.Fixture

/-!
`lake exe leanlight-bench [--runs N] [fixtures...]`: what verifying costs, offline, on recorded
mainnet runs (`fixtures/`, `leanlight record`): no network, so only the light client's own work.
Each step is timed `N` times (default 9), the median printed in milliseconds:

- `bootstrap`: decoding and `Store.bootstrap` (the checkpoint's root and the committee's branch;
  its keys are kept as bytes, not validated);
- `period update`: each `/updates` chunk through `Store.receive` (a signature, and the next
  committee's root);
- `finality`, `optimistic`: one signature each;
- `header`: binding the anchored block's header (`Anchor.bind`: RLP and Keccak-256);
- `reads`: every recorded read's proofs checked (`Driver.read`, `codeOk`).

Each run passes a clock one millisecond later, so the compiler cannot share one result between
runs; every result is checked, so none is skipped.
-/

open LeanLight.Lc LeanLight.Cli LeanLightTests.Fixture

def median (xs : Array Nat) : Nat :=
  let s := xs.qsort (· < ·)
  s[s.size / 2]?.getD 0

/-- `f` run `n` times, each at clock `now + i`, timed: the median, in microseconds. Fails when a
run's result is not `ok`. -/
def timeIt (n now : Nat) (f : Nat → Bool) (what : String) : IO Nat := do
  let mut ts := #[]
  for i in [0:n] do
    let t0 ← IO.monoNanosNow
    let ok := f (now + i)
    if !ok then throw (IO.userError s!"{what}: refused")
    let t1 ← IO.monoNanosNow
    ts := ts.push ((t1 - t0) / 1000)
  return median ts

def ms (us : Nat) : String :=
  if us < 1000 then s!"{us} µs" else s!"{us / 1000}.{(us % 1000) / 100} ms"

def benchFixture (n : Nat) (dir : System.FilePath) : IO Unit := do
  let f ← load dir
  let c := f.chain
  let now := f.now
  let root := f.hexOf "checkpoint"
  let o ← objects f
  let bfork := f.fork "bootstrap_fork"
  let some s0 := Driver.start c root now bfork o.bootstrap
    | throw (IO.userError s!"{dir}: the bootstrap was refused")
  let tBoot ← timeIt n now (fun t => (Driver.start c root t bfork o.bootstrap).isSome) "bootstrap"
  -- each period update, from the store before it
  let mut s := s0
  let mut tUpd := #[]
  for ch in o.chunks do
    let s' := s
    tUpd := tUpd.push (← timeIt n now (fun t =>
      (Driver.feed c s' t .update (.digest ch.digest) ch.ssz).2.isSome) "period update")
    s := (Driver.feed c s now .update (.digest ch.digest) ch.ssz).1
  let sF := s
  let tFin ← timeIt n now (fun t =>
    (Driver.feed c sF t .finality (f.fork "finality_fork") o.finality).2.isSome) "finality"
  s := (Driver.feed c s now .finality (f.fork "finality_fork") o.finality).1
  let sO := s
  let tOpt ← timeIt n now (fun t =>
    (Driver.feed c sO t .optimistic (f.fork "optimistic_fork") o.optimistic).2.isSome) "optimistic"
  s := (Driver.feed c s now .optimistic (f.fork "optimistic_fork") o.optimistic).1
  let rlp ← headerRlp f
  let sA := s
  let tHdr ← timeIt n now (fun t => (Driver.bindAnchor c sA t rlp).isSome) "header"
  -- the reads' inputs, parsed once: parsing JSON is the client's, not the light client's
  let mut inputs : Array (List UInt8 × ByteArray × List (List UInt8 × ByteArray) × Option ByteArray) := #[]
  for r in ← reads f do
    match r.words, r.files with
    | _ :: addrText :: _, proofFile :: rest =>
      let some addr := hexBytes addrText | continue
      let some (nodes, slots) := (proofParts (← readJson f proofFile)).toOption | continue
      let code ← match rest with
        | [cf] => pure (hexBytes (← IO.FS.readFile (f.dir / cf)).trimAscii.toString)
        | _ => pure none
      inputs := inputs.push (addr.data.toList, nodes, slots, code)
    | _, _ => pure ()
  let tReads ← timeIt n now (fun t => inputs.all fun (a, nodes, slots, code) =>
    match Driver.read c sA t rlp a nodes slots with
    | some (_, acct, _) => code.all (Driver.codeOk acct)
    | none => false) "reads"
  let total := tBoot + tUpd.foldl (· + ·) 0 + tFin + tOpt + tHdr + tReads
  IO.println s!"{dir.fileName.getD ""}: {o.chunks.size} period update(s), {inputs.size} reads, median of {n} runs"
  IO.println s!"  bootstrap      {ms tBoot}"
  IO.println s!"  period update  {", ".intercalate (tUpd.toList.map ms)}"
  IO.println s!"  finality       {ms tFin}"
  IO.println s!"  optimistic     {ms tOpt}"
  IO.println s!"  header         {ms tHdr}"
  IO.println s!"  reads          {ms tReads}"
  IO.println s!"  total          {ms total}"

def main (args : List String) : IO UInt32 := do
  let (n, rest) := match args with
    | "--runs" :: k :: r => (k.toNat!, r)
    | r => (9, r)
  let dirs : List System.FilePath :=
    if rest.isEmpty then ["fixtures/mainnet-fresh", "fixtures/mainnet-week"]
    else rest.map System.FilePath.mk
  for d in dirs do benchFixture n d
  return 0
