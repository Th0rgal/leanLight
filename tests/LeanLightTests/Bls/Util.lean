/-!
# Helpers for the BLS tests: hex, reporting, timing

Test-only (`lake exe leanlight-bls-test`), never linked into the wallet.
-/

namespace LeanLight.Tests.Bls

/-- The value of a hex digit, if it is one. -/
def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Hex (an even number of digits, no `0x`) to bytes; a bad digit reads 0. -/
def unhex (s : String) : ByteArray := Id.run do
  let cs := s.toList.toArray
  let mut out := ByteArray.empty
  for i in [0:cs.size / 2] do
    let hi := (hexDigit (cs[2 * i]?.getD '0')).getD 0
    let lo := (hexDigit (cs[2 * i + 1]?.getD '0')).getD 0
    out := out.push (hi * 16 + lo).toUInt8
  return out

/-- Hex digits to a number; a bad digit reads 0. -/
def natOfHex (s : String) : Nat :=
  s.toList.foldl (fun acc c => acc * 16 + (hexDigit c).getD 0) 0

/-- Bytes to lowercase hex. -/
def hex (b : ByteArray) : String :=
  b.foldl (fun s x =>
    let d := "0123456789abcdef".toList
    s.push (d[(x >>> 4).toNat]?.getD '0') |>.push (d[(x &&& 15).toNat]?.getD '0')) ""

/-- Results, counted per suite. -/
structure Tally where
  passed : Nat := 0
  failed : Nat := 0
  failures : Array String := #[]

def Tally.add (t : Tally) (name : String) (ok : Bool) : Tally :=
  if ok then { t with passed := t.passed + 1 }
  else { t with failed := t.failed + 1, failures := t.failures.push name }

def Tally.report (t : Tally) (suite : String) : IO Unit := do
  IO.println s!"SUITE {suite}: {t.passed} passed, {t.failed} failed"
  for f in t.failures do IO.println s!"  FAIL {f}"

/-- Runs `f` `n` times per batch, `reps` batches, and returns the best batch's time per run, in
nanoseconds; every result goes through `sink`, so none is skipped. -/
def timeBest (n reps : Nat) (f : Nat → Nat) : IO Nat := do
  let mut best := 0
  for r in [0:reps] do
    let t0 ← IO.monoNanosNow
    let mut acc := 0
    for i in [0:n] do
      acc := acc + f i
    if acc == 0xdeadbeefdeadbeef then IO.println "sink"
    let t1 ← IO.monoNanosNow
    if r = 0 || t1 - t0 < best then best := t1 - t0
  return best / n

/-- `ns` as milliseconds with two decimals. -/
def ms (ns : Nat) : String :=
  let h := (ns + 5000) / 10000
  s!"{h / 100}.{if h % 100 < 10 then "0" else ""}{h % 100} ms"

end LeanLight.Tests.Bls
