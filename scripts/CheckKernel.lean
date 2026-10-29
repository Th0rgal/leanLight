import Lean

/-!
The kernel replay `scripts/check-kernel.sh` runs from `proofs/`, under `lake env`: each module
named on the command line has its own declarations added again, through Lean's kernel, to the
environment of its imports as their `.olean` files hold it, one module after the other. It is
an audit tool, not a proof, and lives outside the proofs: it needs `unsafe`, as the
toolchain's `leanchecker` does, to read `.olean` files.

`replay` is `replayFromImports` of the toolchain's `leanchecker` (Lean v4.35.0,
`src/lean/LeanChecker.lean`, Copyright (c) 2023 Kim Morrison, Apache 2.0, authors Kim Morrison
and Sebastian Ullrich), unchanged. What differs is how modules are chosen: `leanchecker`
replays every module whose name starts with a name it is given, all at once, so naming
`LeanLightProofs` loads some two hundred environments together (about 46 GB, measured 2026-10-25);
here a name means that module alone, and one environment is held at a time.
-/

open Lean

unsafe def replay (module : Name) : IO Unit := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  -- Load all module data parts (exported, server, private)
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "failed to read module data" else
  let (mod, _) := parts[0]
  let (_, s) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport s mod.imports {} 0 false false (isModule := true)
  let mut newConstants := {}
  -- Collect constants from last ("most private") part, which subsumes all prior ones
  for name in parts[parts.size-1].1.constNames, ci in parts[parts.size-1].1.constants do
    newConstants := newConstants.insert name ci
  discard <| env.toKernelEnv.replay newConstants
  env.freeRegions

unsafe def main (modules : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut failed := 0
  for m in modules do
    try
      replay m.toName
    catch e =>
      IO.eprintln s!"error: the kernel refuses {m}: {e}"
      failed := failed + 1
  return if failed == 0 then 0 else 1
