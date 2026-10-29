import LeanLight.Codec
import LeanLightDev

/-!
# Helpers of the store's tests

Hex, file reading, a tally, and the test chain a vector's `config.txt` describes (the minimal
preset; fork epochs and versions, `BLOB_SCHEDULE` and `SLOT_DURATION_MS` from the vector, so that
the digests are the vector's; genesis at time 0, and mainnet's `MAX_AGE`).
-/

namespace LeanLightTests.Store

open LeanLight.Lc

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def hex (b : ByteArray) : String :=
  b.foldl (fun s x => s.push (hexDigit (x.toNat / 16)) |>.push (hexDigit (x.toNat % 16))) ""

def unhex (s : String) : ByteArray :=
  let s := if s.startsWith "0x" then s.drop 2 |>.toString else s
  let ds := s.trimAscii.toString.toList.map fun c =>
    if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87
  let rec go : List Nat → Array UInt8 → Array UInt8
    | a :: b :: rest, acc => go rest (acc.push (16 * a + b).toUInt8)
    | _, acc => acc
  ⟨go ds #[]⟩

structure Tally where
  passed : Nat := 0
  failures : Array String := #[]
  unsupported : Array String := #[]

def Tally.check (t : Tally) (ok : Bool) (what : String) : Tally :=
  if ok then { t with passed := t.passed + 1 } else { t with failures := t.failures.push what }

def Tally.skip (t : Tally) (what : String) : Tally := { t with unsupported := t.unsupported.push what }

/-- The words of each non-empty line. -/
def linesOf (text : String) : List (List String) :=
  (text.splitOn "\n").filterMap fun l =>
    let ws := (l.splitOn " ").filter (· ≠ "")
    if ws.isEmpty then none else some ws

def natOf (s : String) : Nat := s.toNat?.getD 0

/-- The chain a vector's `config.txt` describes. -/
def chainOf (config : String) (gvr : ByteArray) : Forks.Chain := Id.run do
  let ls := linesOf config
  let val (k : String) : Option String :=
    (ls.find? fun ws => ws.head? == some k).bind (·[1]?)
  let mut forks : List Forks.Fork := []
  for (name, key) in [(Forks.ForkName.electra, "ELECTRA"), (.fulu, "FULU"), (.gloas, "GLOAS")] do
    match val s!"{key}_FORK_EPOCH", val s!"{key}_FORK_VERSION" with
    | some e, some v =>
      if natOf e < Forks.farFuture then forks := forks ++ [⟨name, natOf e, unhex v⟩]
    | _, _ => pure ()
  let blobs := ls.filterMap fun ws =>
    if ws.head? == some "BLOB" then some (natOf (ws[1]?.getD "0"), natOf (ws[2]?.getD "0")) else none
  return { chainId := 0, preset := Dev.minimalPreset, genesisValidatorsRoot := gvr, genesisTime := 0,
           forks, maxBlobsElectra := natOf ((val "MAX_BLOBS_PER_BLOCK_ELECTRA").getD "9"),
           blobSchedule := blobs,
           slotSchedule := [(0, natOf ((val "SLOT_DURATION_MS").getD "6000"))],
           maxAge := Forks.maxAge14d }

/-- The minimal preset's codec. -/
def codec : Codec.Codec := Dev.codec Dev.minimalPreset

end LeanLightTests.Store
