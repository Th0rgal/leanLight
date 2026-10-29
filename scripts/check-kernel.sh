#!/usr/bin/env bash
# Replays every module of LeanLight and LeanLightProofs through Lean's kernel, one module at a
# time (scripts/CheckKernel.lean, the toolchain's leanchecker's replay), so a proof accepted with
# the kernel skipped (`debug.skipKernelTC`, a tool that elaborates without it) fails here.
# Run after `lake build` in proofs/. LEANLIGHT_KERNEL_JOBS sets the parallelism (default 4).
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root/proofs"
jobs=${LEANLIGHT_KERNEL_JOBS:-4}

if grep -rnE 'set_option[[:space:]]+debug\.|skipKernelTC' --include='*.lean' "$root/LeanLight" "$root/proofs/LeanLightProofs"; then
  echo "error: a debug option above can let a false proof past the kernel; none is allowed" >&2
  exit 1
fi

modules=$(
  { (cd "$root" && find LeanLight -name '*.lean' && echo LeanLight.lean)
    find LeanLightProofs -name '*.lean'; echo LeanLightProofs.lean; } | sed 's/\.lean$//; s|/|.|g'
)
# One `lake env` up front: concurrent ones contend for Lake's configuration lock.
leanpath=$(lake env printenv LEAN_PATH)
count=$(wc -l <<<"$modules")
start=$(date +%s)
if ! sort -u <<<"$modules" | LEAN_PATH=$leanpath xargs -P "$jobs" -n 16 lean --run "$root/scripts/CheckKernel.lean"; then
  echo "error: the kernel refused a module above" >&2
  exit 1
fi
echo "kernel replay passed: $count modules in $(($(date +%s) - start)) s"
