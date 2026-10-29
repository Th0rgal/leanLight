/-
Copyright (c) 2025 Ethereum Foundation. All rights reserved.
Released under the MIT license as described in the file `LeanLightProofs/Vendor/SszSpecs/LICENSE`.

`lean/Ssz/Proofs/Codec/Layout.lean` of github.com/ethereum/ssz-specs at commit
`3394318c67b08896a5406e15f10e02508a2f1332`, vendored as a specification
(leanKohakuDesktop's spec/16-light-client.md, "Sources"): ssz-specs does not build as a Lake dependency on Lean
4.35, its lakefile turning deprecation warnings into errors; in this package, which does not,
they stay warnings. Nothing of it runs in the wallet. Repairs: its imports `Ssz.*` are renamed
`LeanLightProofs.Vendor.SszSpecs.Ssz.*`.
-/
import LeanLightProofs.Vendor.SszSpecs.Ssz.Codec.Layout
import LeanLightProofs.Vendor.SszSpecs.Ssz.Proofs.Merkle.Tree

/-! Laws of the layout that places a progressive container's fields around its gaps. -/

namespace Ssz

/-- A successful layout preserves every field in order and has one slot per position. -/
private theorem placeSlots_preserves {active : List Bool} {fields : List (Desc × Value)}
    {slots : List (Option (Desc × Value))} (placed : placeSlots active fields = .ok slots) :
    slots.filterMap id = fields ∧ slots.length = active.length := by
  induction active generalizing fields slots with
  | nil =>
    -- With no positions left, success requires no fields left either.
    cases fields <;> simp_all [placeSlots]
  | cons bit active ih =>
    cases bit with
    | false =>
      -- Removing a gap keeps the field sequence and shortens the layout by one.
      cases tail : placeSlots active fields <;>
        simp [placeSlots, tail, Bind.bind, Except.bind, pure, Except.pure] at placed
      subst slots
      simpa using ih tail
    | true =>
      -- An occupied position keeps the first field and delegates the remaining positions.
      cases fields with
      | nil => simp [placeSlots] at placed
      | cons field fields =>
        cases tail : placeSlots active fields <;>
          simp [placeSlots, tail, Bind.bind, Except.bind, pure, Except.pure] at placed
        subst slots
        obtain ⟨ordered, sized⟩ := ih tail
        simp [ordered, sized]

/-- Removing gaps from a successful layout recovers the declared fields in order. -/
theorem placeSlots_fields {active : List Bool} {fields : List (Desc × Value)}
    {slots : List (Option (Desc × Value))} (placed : placeSlots active fields = .ok slots) :
    slots.filterMap id = fields :=
  -- Field preservation follows independently of the number of gaps.
  (placeSlots_preserves placed).1

end Ssz
