import LeanLightProofs
import Lean

/-!
The axiom audit, run by `scripts/check-axioms.sh`: every constant declared in a `LeanLight` or
`LeanLightProofs` module, theorem or definition, may rest only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). A `sorry` (`sorryAx`), `native_decide`
(`Lean.ofReduceBool`) or any new axiom fails it. Nothing is listed by hand, so a new theorem
cannot be left out.
-/

open Lean Elab Command

elab "#audit_leanlight" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  let mut theorems := 0
  let mut bad : Array (Name × Array Name) := #[]
  for (nm, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? nm | continue
    let root := env.header.moduleNames[idx.toNat]!.getRoot
    unless root == `LeanLight || root == `LeanLightProofs do continue
    if nm.isInternal then continue
    checked := checked + 1
    if ci matches .thmInfo _ then theorems := theorems + 1
    let axs ← liftCoreM (Lean.collectAxioms nm)
    let extra := axs.filter (fun a => !allowed.contains a)
    unless extra.isEmpty do bad := bad.push (nm, extra)
  for (nm, axs) in bad do
    logError m!"{nm} depends on {axs}"
  logInfo m!"audited {checked} constants ({theorems} theorems): {bad.size} outside the allowed axioms"

#audit_leanlight
