import LeanLightCli.Client

/-!
# `leanlight`

```
leanlight [--network mainnet|sepolia] --consensus-rpc URL [--execution-rpc URL]
          [--checkpoint 0xROOT] [--json] [-v] COMMAND
COMMAND:
  sync                    sync and print the finalized and anchored heads
  block-number            the anchored execution block's number
  balance ADDR            the account's balance (wei), proved
  nonce ADDR              the account's nonce, proved
  code ADDR               the code's hash and size, the code checked against the proved hash
  storage ADDR SLOT...    storage words, proved
  queries FILE            one sync, then each line of FILE ("balance 0x..", "nonce 0x..",
                          "code 0x..", "storage 0x.. 0xSLOT..", "block-number")
```

Every value printed comes out of `LeanLight`'s checked readers. Timings go to standard error
(or into the JSON lines with `--json`): wall time, time waiting on the network, time verifying.
-/

open LeanLight.Cli
open LeanLight.Lc

structure Args where
  network : String := "mainnet"
  consensus : Option String := none
  execution : Option String := none
  checkpoint : Option String := none
  json : Bool := false
  verbose : Bool := false
  rest : List String := []

partial def parseArgs : List String → Args → Except String Args
  | [], a => pure { a with rest := a.rest.reverse }
  | "--network" :: v :: r, a => parseArgs r { a with network := v }
  | "--consensus-rpc" :: v :: r, a => parseArgs r { a with consensus := some v }
  | "--execution-rpc" :: v :: r, a => parseArgs r { a with execution := some v }
  | "--checkpoint" :: v :: r, a => parseArgs r { a with checkpoint := some v }
  | "--json" :: r, a => parseArgs r { a with json := true }
  | "-v" :: r, a => parseArgs r { a with verbose := true }
  | x :: r, a =>
    if x.startsWith "--" then throw s!"unknown option {x}" else parseArgs r { a with rest := x :: a.rest }

def usage : String :=
  "usage: leanlight [--network mainnet|sepolia] --consensus-rpc URL [--execution-rpc URL] " ++
  "[--checkpoint 0xROOT] [--json] [-v] (sync | block-number | balance ADDR | nonce ADDR | " ++
  "code ADDR | storage ADDR SLOT... | queries FILE)"

def jstr (s : String) : String := (Lean.Json.str s).compress

def emit (json : Bool) (fields : List (String × String)) (text : String) : IO Unit := do
  if json then
    IO.println ("{" ++ ", ".intercalate (fields.map fun (k, v) => s!"{jstr k}: {v}") ++ "}")
  else IO.println text

def hexArg (what s : String) : IO ByteArray := do
  match hexBytes s with
  | some b => pure b
  | none => die s!"{what}: not hex: {s}"

def addrArg (s : String) : IO ByteArray := do
  let b ← hexArg "address" s
  if b.size != 20 then die s!"address: not 20 bytes: {s}"
  pure b

def slotArg (s : String) : IO ByteArray := do
  let b ← hexArg "slot" s
  if b.size > 32 then die s!"slot: more than 32 bytes: {s}"
  pure (ByteArray.mk (List.replicate (32 - b.size) (0 : UInt8)).toArray ++ b)

/-- One read at the anchored block; returns the JSON fields and the text line. -/
def runQuery (cfg : Config) (b : Anchored) (q : List String) :
    IO (List (String × String) × String) := do
  let blk := b.el.number
  match q with
  | ["block-number"] => pure ([("q", jstr "block-number"), ("value", toString blk)], s!"{blk}")
  | ["balance", a] =>
    let r ← readAccount cfg b (← addrArg a) []
    pure ([("q", jstr "balance"), ("addr", jstr a), ("block", toString blk),
      ("value", jstr (natHex r.account.balance))], s!"{r.account.balance}")
  | ["nonce", a] =>
    let r ← readAccount cfg b (← addrArg a) []
    pure ([("q", jstr "nonce"), ("addr", jstr a), ("block", toString blk),
      ("value", jstr (natHex r.account.nonce))], s!"{r.account.nonce}")
  | ["code", a] =>
    let addr ← addrArg a
    let r ← readAccount cfg b addr []
    let code ← readCode cfg b addr r.account.codeHash
    pure ([("q", jstr "code"), ("addr", jstr a), ("block", toString blk),
      ("value", jstr (toHexL r.account.codeHash)), ("size", toString code.size)],
      s!"{toHexL r.account.codeHash} ({code.size} bytes)")
  | "storage" :: a :: slots =>
    if slots.isEmpty then die "storage: no slot"
    let ss ← slots.mapM slotArg
    let r ← readAccount cfg b (← addrArg a) ss
    let words := r.slots.map fun v => toHexL (beN 32 v)
    pure ([("q", jstr "storage"), ("addr", jstr a), ("block", toString blk),
      ("slots", (Lean.Json.arr (slots.toArray.map Lean.Json.str)).compress),
      ("value", (Lean.Json.arr (words.toArray.map Lean.Json.str)).compress)],
      " ".intercalate words)
  | _ => die s!"unknown query: {" ".intercalate q}"

def timed {α} (act : IO α) : IO (α × Nat × Timing) := do
  timing.set {}
  let t0 ← IO.monoMsNow
  let a ← act
  let t1 ← IO.monoMsNow
  return (a, t1 - t0, ← timing.get)

def timingFields (ms : Nat) (t : Timing) : List (String × String) :=
  [("ms", toString ms), ("net_ms", toString t.netMs), ("verify_ms", toString t.verifyMs),
   ("requests", toString t.requests), ("bytes", toString t.bytes)]

def timingText (ms : Nat) (t : Timing) : String :=
  s!"{ms} ms (network {t.netMs} ms in {t.requests} requests, {t.bytes} bytes; verify {t.verifyMs} ms)"

def main (argv : List String) : IO UInt32 := do
  let args ← match parseArgs argv {} with
    | .ok a => pure a
    | .error e => IO.eprintln e; IO.eprintln usage; return 2
  verbose.set args.verbose
  let some chain := (match args.network with
      | "mainnet" => some Forks.mainnet
      | "sepolia" => some Forks.sepolia
      | _ => none)
    | IO.eprintln s!"unknown network {args.network}"; return 2
  let some consensus := args.consensus | IO.eprintln usage; return 2
  let checkpoint ← args.checkpoint.mapM (hexArg "checkpoint")
  let cfg : Config := { chain, consensus, execution := args.execution.getD "", checkpoint }
  try
    let (sy, ms, t) ← timed (sync cfg)
    let s := sy.store
    let anchor := s.anchor.map (·.header.beacon.slot)
    emit args.json ([("phase", jstr "sync"), ("finalized_slot", toString s.finalized.beacon.slot),
        ("anchor_slot", toString (anchor.getD 0)), ("updates", toString sy.updates),
        ("accepted", toString sy.accepted),
        ("refused", (Lean.Json.arr (sy.refused.reverse.toArray.map Lean.Json.str)).compress)] ++
        timingFields ms t)
      s!"synced: finalized slot {s.finalized.beacon.slot}, anchor slot {anchor.getD 0}, {sy.updates} updates ({sy.accepted} accepted{if sy.refused.isEmpty then "" else s!", refused: {sy.refused.reverse}"}) in {timingText ms t}"
    match args.rest with
    | [] | ["sync"] => pure ()
    | ["queries", file] =>
      let lines := (← IO.FS.lines file).toList.filter fun l =>
        let l := l.trimAscii.toString
        !l.isEmpty && !l.startsWith "#"
      let (b, ms, t) ← timed (anchoredBlock cfg s)
      emit args.json ([("phase", jstr "anchor"), ("block", toString b.el.number),
          ("hash", jstr (toHex b.hash))] ++ timingFields ms t)
        s!"anchored block {b.el.number} {toHex b.hash} in {timingText ms t}"
      for l in lines do
        let q := (l.trimAscii.toString.splitOn " ").filter (· ≠ "")
        try
          let ((fs, text), ms, t) ← timed (runQuery cfg b q)
          emit args.json (fs ++ timingFields ms t) s!"{l.trimAscii}: {text}   [{timingText ms t}]"
        catch e =>
          emit args.json [("q", jstr l.trimAscii.toString), ("error", jstr (toString e))]
            s!"{l.trimAscii}: error: {e}"
    | q =>
      let ((fs, text), ms, t) ← timed do
        let b ← anchoredBlock cfg s
        runQuery cfg b q
      emit args.json (fs ++ timingFields ms t) text
      unless args.json do IO.eprintln s!"read in {timingText ms t}"
    cleanup
    return 0
  catch e =>
    cleanup
    IO.eprintln s!"error: {e}"
    return 1
