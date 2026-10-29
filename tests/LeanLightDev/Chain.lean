import LeanLightDev.Minimal

/-!
# The development table

The chain the development builds' fake beacon serves (leanKohakuDesktop's `spec/16-light-client.md`, "Testing"):
the minimal preset, one-second slots, Electra at epoch 0, Fulu at 1 and Gloas at 2, or at the
epoch the fake beacon asks, or never (the minimal configuration's versions), and a `MAX_AGE` of ten minutes, so that the e2e tests reach "too old".
Never in a release.
-/

namespace LeanLight.Lc.Dev

open LeanLight.Lc.Forks (Chain)
open LeanLight.Lc.Ssz (bytesOf)

/-- `MAX_AGE` on the development chain: ten minutes. -/
def devMaxAge : Nat := 600000

/-- The development table for chain `chainId`, its genesis validators root and genesis time
(seconds) the fake beacon's, and its Gloas fork's epoch (`none`: never, so every header names
its own payload; LC5's table has it at 2). Fulu is at epoch 1 unless Gloas comes first. -/
def devChain (chainId : Nat) (gvr : ByteArray) (genesisTime : Nat) (gloas : Option Nat := some 2) :
    Chain :=
  { chainId, preset := minimalPreset, genesisValidatorsRoot := gvr, genesisTime,
    forks := [⟨.electra, 0, bytesOf [0x05, 0, 0, 0x01]⟩] ++
      (if gloas.any (· ≤ 1) then [] else [⟨.fulu, 1, bytesOf [0x06, 0, 0, 0x01]⟩]) ++
      gloas.toList.map fun e => ⟨.gloas, e, bytesOf [0x07, 0, 0, 0x01]⟩,
    maxBlobsElectra := 9, blobSchedule := [], slotSchedule := [(0, 1000)], maxAge := devMaxAge }

end LeanLight.Lc.Dev
