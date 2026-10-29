import LeanLightTests.Bls.Differential
import LeanLightTests.Bls.Provenance

/-!
# `lake exe leanlight-bls-test`: BLS12-381's vectors, differential tests and timings

leanKohakuDesktop's `spec/16-light-client.md`, "Testing": every vector of `LeanLightTests.Bls.Vectors` on the light
client's layer (`LeanLight.Bls`) and on EthLib's readable layer (`LeanLightProofs.Vendor.EthLib.Bls`); the
hash-to-curve constants' provenance; the benchmark's self-tests; mutated keys, signatures and
messages refused; the two layers compared on inputs no vector has; the timings of an update and
of a committee's KeyValidates.

Exits 0 when every check passes. `--budget` also fails when an update takes more than 20 ms
(LC4a's acceptance, on the machine of `spec/16`'s "Speed"); `--quick` skips the timings.
-/

open LeanLight.Tests.Bls

def main (args : List String) : IO UInt32 := do
  let z := (← IO.monoNanosNow) % 1
  let mut failed := 0
  for (L, suite) in [(runtime, "runtime"), (readable, "readable")] do
    let t ← vectors L
    t.report s!"vectors, {suite} layer"
    failed := failed + t.failed
  let pv := provenance
  pv.report "provenance of the hash-to-curve constants"
  failed := failed + pv.failed
  let st ← selfTests z
  st.report "self-tests, runtime layer"
  failed := failed + st.failed
  let df ← differential z
  df.report "differential, runtime and readable layers"
  failed := failed + df.failed
  unless args.contains "--quick" do
    let (tt, update, _) ← timings z 9
    tt.report "timed cases, runtime layer"
    failed := failed + tt.failed
    if args.contains "--budget" && update > 20000000 then
      IO.println "FAIL an update took more than 20 ms"
      failed := failed + 1
    -- For reference: EthLib's readable layer on one vector (not a budget).
    let v := (Vectors.ethFav.filter fun v => v.output && !v.pubkeys.isEmpty).headD
      { name := "", pubkeys := [], message := "", signature := "", output := false }
    let pks := v.pubkeys.map unhex
    let ns ← timeBest 1 2 fun i =>
      if readable.ethFav pks (unhex v.message) (if i = 1000 then ByteArray.empty else unhex v.signature)
      then 1 else 0
    IO.println s!"TIME readable layer (EthLib), eth_fast_aggregate_verify of {v.name}: {ms ns}"
  IO.println s!"ALL {if failed = 0 then "ok" else s!"FAILED ({failed})"}"
  return (if failed = 0 then 0 else 1)
