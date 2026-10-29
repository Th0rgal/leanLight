import LeanLightTests.Store.Vectors

/-!
`lake exe leanlight-store-test [vectors/light_client]`: `LeanLight.Store` against consensus-specs'
minimal-preset `sync` and `update_ranking` vectors (`LeanLightTests.Store.Vectors`). Steps that
force an update are reported unsupported, not failed. Exits 1 on any failure.
-/

open LeanLightTests.Store

def main (args : List String) : IO UInt32 := do
  let root : System.FilePath := args.headD "vectors/light_client"
  let t ← runVectors root {}
  for f in t.failures do IO.println s!"FAIL {f}"
  for u in t.unsupported do IO.println s!"unsupported: {u}"
  IO.println s!"{t.passed} checks passed, {t.failures.size} failed, {t.unsupported.size} unsupported"
  return if t.failures.isEmpty then 0 else 1
