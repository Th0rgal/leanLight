import LeanLightProofs.Vendor.VCVio.Sha2

/-!
# SHA-256 specification

SHA-256 as FIPS 180-4 defines it: the initial hash value of §5.3.3, the constants of §4.2.2,
the functions Ch, Maj, Σ0, Σ1, σ0, σ1 of §4.1.2, the padding of §5.1.1 and the computation of
§6.2.2.

The specification is VCVio's pure-Lean SHA-256 (`SLHDSA.Concrete.Sha2`), vendored unchanged in
`LeanLightProofs/Vendor/VCVio/Sha2.lean` until VCVio and Aeneas share a Lean version. Reviewing it
against FIPS 180-4 means checking, in that file: `iv` and `k` (the constants), `rotr`, `ch`,
`maj`, `bsig0`, `bsig1`, `ssig0`, `ssig1` (the functions, with the rotation amounts of §4.1.2),
`pad` (append `0x80`, zeros, and the bit length as 8 big-endian bytes, to a multiple of 64
bytes), `compress` (the message schedule from 16 big-endian words, the 64 rounds, and the
final addition), and `stateBytes32` (the eight words, big-endian). It reproduces the NIST
example digests of `""`, `"abc"` and the 448-bit message, and `lkd_verified::sha256`'s tests
check further lengths around the padding boundaries against OpenSSL.
-/

namespace LeanLight.Spec.Sha256

/-- SHA-256 of a byte string: VCVio's `sha256`. -/
abbrev sha256 : ByteArray → ByteArray := SLHDSA.Concrete.Sha2.sha256

end LeanLight.Spec.Sha256
