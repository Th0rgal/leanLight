import Lean.Elab.Command
import Lean.Meta.Tactic.Delta

/-!
# `value_eq`: a definition equals its value, unapplied

`value_eq thm : f` adds the theorem `thm : f = <the value of f>`, proved by `Eq.refl f`.

Why not `f.eq_1 : f x = body x`, or `unfold f`: when `body` begins with a `match` (after its
`let`s), the kernel, checking `f x ≡ body x`, unfolds the matcher before `f` (matchers are
abbreviations, which it unfolds first) and then reduces the matcher's discriminant to a
constructor, evaluating it. For `hash_to_G2` and SSWU that discriminant computes SHA-256 and
square roots (`Nat.powMod`) on symbolic arguments, and the kernel runs out of stack. Comparing
the constant `f` itself with a `fun`, the kernel can only unfold `f`, after which both sides are
the same term. The matches in the value are then rewritten by lemmas about the matcher applied to
variables (`Option.elim`, `if`), which the kernel checks without reducing anything.

The theorem is checked by the kernel like any other (`scripts/check-kernel.sh` replays it).
-/

open Lean Elab Command Meta in
/-- `value_eq thm : f` declares `thm : f = <value of f>` in the current namespace, by `rfl`. -/
elab "value_eq " thm:ident " : " c:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let info ← getConstInfoDefn n
  let lhs := Expr.const n (info.levelParams.map Level.param)
  let type ← mkEq lhs info.value
  let value ← mkEqRefl lhs
  let name := (← getCurrNamespace) ++ thm.getId
  let tv : TheoremVal :=
    { name := name, levelParams := info.levelParams, type := type, value := value }
  addDecl (Declaration.thmDecl tv)

open Lean Elab Tactic Meta in
/-- `delta_private` unfolds, in the goal, every private definition of any module that is not a
matcher: a vendored file's private helpers (EthLib's `i2osp`, `strxor`) cannot be named from
another module, so cannot be unfolded by name. The new goal is the old one up to delta, checked
by the kernel. Matchers are left alone, for the reason `value_eq` gives. -/
elab "delta_private" : tactic => liftMetaTactic1 fun g => do
  let env ← getEnv
  some <$> g.deltaTarget fun n => isPrivateName n && !(isMatcherCore env n)
