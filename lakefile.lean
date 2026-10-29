import Lake
open Lake DSL

/-!
leanLight: an Ethereum consensus light client written in Lean 4, with its proofs.

* `LeanLight`: the light client itself, imports nothing beyond Lean core: SHA-256, Keccak-256,
  RLP, SSZ, BLS12-381, the sync protocol's store, execution-layer headers, Merkle-Patricia proofs
  and the reads anchored on a verified beacon header. It runs compiled (GMP `Nat` for BLS).
* `leanlight`: a command-line client over `LeanLight` that fetches from a beacon API and an
  execution JSON-RPC endpoint with `curl`, and checks every answer with `LeanLight`.
* The proofs live in `proofs/`, a package of their own that requires Mathlib and this package.
-/

package leanlight where
  leanOptions := #[⟨`autoImplicit, false⟩]

/-- The light client, Lean core only. `lake build LeanLight:static` builds a static library. -/
@[default_target] lean_lib LeanLight where
  libName := "leanlight"

/-- The command-line client's modules (HTTP through `curl`, JSON, the commands). -/
lean_lib LeanLightCli

/-- `leanlight`: sync from a checkpoint and answer verified reads (see `README.md`). -/
@[default_target] lean_exe leanlight where
  root := `Main
