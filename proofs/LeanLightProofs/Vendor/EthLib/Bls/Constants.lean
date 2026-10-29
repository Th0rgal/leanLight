/-!
# BLS12-381, readable layer: `Constants`

Derived from `EthLib/Cryptography/Bls/Constants.lean` of github.com/ethereum/EthLib at commit
`57af539e81b8c6f0f54c8b4da3adbc77b122a100`, which its authors dedicated to the public domain
under CC0-1.0 (`LeanLightProofs/Vendor/EthLib/LICENSE`). Rewritten to the Runtime Lean rules:
`partial` definitions take fuel or recurse structurally, `a[i]!` is `a[i]?.getD 0`, panics return
`Except`, `while` loops are bounded `for` loops. Left out: the two `@[export]` size accessors for EthLib's Python C extension. No semantic change.

It is the specification `LeanLight.Bls` is to be proved equal to (`docs/spec-16-light-client.md`,
invariant 25c, LC4b), not code the wallet runs; it imports nothing beyond Lean core, so
`tests` compiles it into the test executable that runs both layers on the vectors. Its
imports and its namespace are EthLib's, the module paths moved under `LeanLightProofs.Vendor.EthLib`.
-/

namespace EthLib.Cryptography.Bls.Constants

/-- Number of bytes in a serialized G1 pubkey (compressed). -/
def BYTES_PER_PUBKEY : Nat := 48

/-- Number of bytes in a serialized G2 signature (compressed). -/
def BYTES_PER_SIGNATURE : Nat := 96

end EthLib.Cryptography.Bls.Constants
