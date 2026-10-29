/-!
# BLS12-381, readable layer: `Errors`

Derived from `EthLib/Cryptography/Bls/Errors.lean` of github.com/ethereum/EthLib at commit
`57af539e81b8c6f0f54c8b4da3adbc77b122a100`, which its authors dedicated to the public domain
under CC0-1.0 (`LeanLightProofs/Vendor/EthLib/LICENSE`). Rewritten to the Runtime Lean rules:
`partial` definitions take fuel or recurse structurally, `a[i]!` is `a[i]?.getD 0`, panics return
`Except`, `while` loops are bounded `for` loops. Left out: `runBls` (`IO`, for EthLib's C ABI) and `panicWith` (a panic, used by no BLS definition). Added: the error `sswuNoRoot`, which `HashToCurve.simpleSwu` returns where EthLib panicked.

It is the specification `LeanLight.Bls` is to be proved equal to (leanKohakuDesktop's `spec/16-light-client.md`,
invariant 25c, LC4b), not code the wallet runs; it imports nothing beyond Lean core, so
`tests` compiles it into the test executable that runs both layers on the vectors. Its
imports and its namespace are EthLib's, the module paths moved under `LeanLightProofs.Vendor.EthLib`.
-/

/-!
# `Bls.Errors`

Typed errors for the BLS surface.

The BLS spec functions do no I/O, so the fallible ones return
`Except BlsError` and report structured failures rather than
stringly-typed `IO.userError`s. EthLib's C-ABI layer runs such a
computation down to `IO`; that layer is not vendored.
-/

namespace EthLib.Cryptography.Bls

/-- Every way a BLS operation can reject its input. -/
inductive BlsError where
  /-- The pubkey list was empty. -/
  | emptyPubkeyList
  /-- A pubkey was not `BYTES_PER_PUBKEY` bytes long. -/
  | badPubkeySize (actual : Nat)
  /-- Pubkey bytes failed `KeyValidate` (bad encoding, off-curve, wrong
  subgroup, or the point at infinity). When it came from an array,
  `index` is its position. -/
  | invalidPubkey (index : Option Nat)
  /-- G1 point bytes could not be decompressed. -/
  | invalidG1Point
  /-- G2 point bytes could not be decompressed. -/
  | invalidG2Point
  /-- `KeyValidate` rejected the point at infinity. -/
  | pointAtInfinity
  /-- A point was not in the prime-order subgroup. -/
  | notInSubgroup
  /-- Bytes did not represent a canonical field element (value ≥ modulus). -/
  | nonCanonicalFieldElement
  /-- A field element had no square root (not a quadratic residue). -/
  | notASquare
  /-- `expand_message_xmd` was asked for more than 65535 bytes. -/
  | expandMessageOutputTooLong (len : Nat)
  /-- `expand_message_xmd` would need more than 255 hash blocks. -/
  | expandMessageTooManyBlocks (ell : Nat)
  /-- The simplified SWU map found no square root (never, for RFC 9380's `Z`; EthLib
  panicked here). -/
  | sswuNoRoot

/-- Human-readable description, used at the C-ABI boundary. -/
def BlsError.message : BlsError → String
  | .emptyPubkeyList            => "empty pubkey list"
  | .badPubkeySize actual       => s!"bad pubkey size: {actual}"
  | .invalidPubkey (some index) => s!"invalid pubkey at index {index}"
  | .invalidPubkey none         => "invalid pubkey"
  | .invalidG1Point             => "invalid G1 point"
  | .invalidG2Point             => "invalid G2 point"
  | .pointAtInfinity            => "point at infinity"
  | .notInSubgroup              => "point not in subgroup"
  | .nonCanonicalFieldElement   => "non-canonical field element"
  | .notASquare                 => "not a square"
  | .expandMessageOutputTooLong len =>
      s!"expand_message_xmd output too long: {len}"
  | .expandMessageTooManyBlocks ell =>
      s!"expand_message_xmd too many blocks: {ell}"
  | .sswuNoRoot => "simplified SWU found no square root"

end EthLib.Cryptography.Bls
