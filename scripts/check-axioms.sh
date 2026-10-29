#!/usr/bin/env bash
# Fails if any constant of LeanLight or LeanLightProofs rests on `sorry`, `native_decide` or an
# axiom beyond propext, Classical.choice and Quot.sound (proofs/Audit.lean).
set -euo pipefail
cd "$(dirname "$0")/../proofs"
lake build >/dev/null
out=$(lake env lean Audit.lean 2>&1) || { echo "$out"; exit 1; }
echo "$out"
grep -q ': 0 outside the allowed axioms' <<<"$out" || { echo "error: axiom audit failed" >&2; exit 1; }
echo "axiom check passed"
