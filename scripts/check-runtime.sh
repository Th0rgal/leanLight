#!/usr/bin/env bash
# Fails if the light client's runtime code (LeanLight/) could run something its proofs are not
# about: `@[implemented_by]` and `@[extern]` swap in other code with no proof obligation, `opaque`
# hides a definition from the proofs, `unsafe` and `partial` escape the logic. A fast version may
# replace a readable one only through a proved `@[csimp]` equation, which the axiom audit
# (check-axioms.sh) covers; the equations are listed here.
set -euo pipefail
cd "$(dirname "$0")/.."
# Matches at the start of a line only: prose in comments naming the attributes is not code.
bad=$(grep -rnE '^\s*(@\[(implemented_by|extern)|(private |protected |noncomputable )*(opaque|unsafe|partial) )' \
  --include='*.lean' LeanLight LeanLight.lean || true)
if [ -n "$bad" ]; then
  echo "$bad"
  echo "error: runtime code outside what the proofs cover" >&2
  exit 1
fi
echo "csimp equations (each a theorem the axiom audit checks):"
grep -rn '@\[csimp\]' --include='*.lean' LeanLight | sed 's/:.*theorem / /; s/ :.*//'
echo "runtime check passed"
