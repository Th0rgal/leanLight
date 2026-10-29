/-
Copyright (c) 2025 Ethereum Foundation. All rights reserved.
Released under the MIT license as described in the file `LeanLightProofs/Vendor/SszSpecs/LICENSE`.

`lean/Ssz/Merkle/Chunk.lean` of github.com/ethereum/ssz-specs at commit
`3394318c67b08896a5406e15f10e02508a2f1332`, vendored as a specification
(docs/spec-16-light-client.md, "Sources"): ssz-specs does not build as a Lake dependency on Lean
4.35, its lakefile turning deprecation warnings into errors; in this package, which does not,
they stay warnings. Nothing of it runs in the wallet. Repairs: none.
-/
/-! The width of a tree node. -/

namespace Ssz

/--
Width of a tree node in bytes.

The specification fixes it at the width of the hash output.
-/
abbrev bytesPerChunk : Nat :=
  32

/-- Width of a tree node in bits. -/
abbrev bitsPerChunk : Nat :=
  8 * bytesPerChunk

end Ssz
