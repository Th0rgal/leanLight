import LeanLight.Base.Keccak
import LeanLight.Base.KeccakFast

/-!
# Keccak-256 over lists of bytes

The one definition of `LeanLightProofs.Spec.Common` that runtime code needs too: the light client's
header check (`LeanLight.El.Header`) hashes the header's bytes with it. It lives here, in the base
library both `keyd`'s core and the light client import, in `Spec.Common`'s namespace, so every
module that `export`s `Common (keccak)` names this one definition.
-/

namespace LeanLight.Spec.Common

/-- Keccak-256 of a list of bytes, as a list of bytes (32 of them): the EVM's `keccak256`,
`Spec.Keccak.keccak256`, which `Spec.Keccak.keccak256_eq_vcvio` proves to be VCVio's. -/
def keccak (bs : List UInt8) : List UInt8 := (Spec.Keccak.keccak256 ⟨bs.toArray⟩).data.toList

end LeanLight.Spec.Common
