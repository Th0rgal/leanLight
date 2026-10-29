import LeanLight.Codec

/-!
# The minimal preset

consensus-specs' minimal preset (`presets/minimal`): 8 slots an epoch, 8 epochs a sync committee
period, 32 committee members. Its light-client containers differ from the mainnet preset's only
in the sizes of `SyncCommittee` (33 keys) and `SyncAggregate` (32 bits), so the decoders here
are `LeanLight.Ssz`'s with the committee's size a parameter, decoding straight into the store's
objects (`codec`). They run in the tests (`leanlight-store-test`, the minimal-preset vectors) and,
later, the development builds' fake beacon; never in a release (`LeanLightDev`, `dev-insecure`).
They are tested against the vectors, not proved.
-/

namespace LeanLight.Lc.Dev

open LeanLight.Lc.Ssz (BeaconBlockHeader SyncCommittee SyncAggregate ExecutionPayloadHeader u64
  offsetAt slice roots fields)
open LeanLight.Lc.Forks (Preset ForkName)
open LeanLight.Lc.Store (Header Update Bootstrap)
open LeanLight.Lc.Codec (Kind Codec emptyCommittee zeroBranch emptyElectra emptyGloas ofElectra ofGloas)
open LeanLight.Lc.Bytes (extract)

/-- The minimal preset. -/
def minimalPreset : Preset := ⟨8, 8, 32, 5⟩

variable (p : Preset)

/-- A `SyncCommittee`'s size: the keys and the aggregate, 48 bytes each. -/
def committeeSize : Nat := 48 * p.committeeSize + 48

/-- A `SyncAggregate`'s size: the bits, then the signature. -/
def aggregateSize : Nat := p.committeeSize / 8 + 96

def readCommittee (bs : ByteArray) : SyncCommittee :=
  { pubkeys := fields bs 0 48 p.committeeSize, aggregatePubkey := slice bs (48 * p.committeeSize) 48 }

def readAggregate (bs : ByteArray) : SyncAggregate :=
  { bits := slice bs 0 (p.committeeSize / 8), signature := slice bs (p.committeeSize / 8) 96 }

/-! ## Electra and Fulu -/

namespace Electra

def bootstrap (bs : ByteArray) : Option Bootstrap :=
  let fixed := 4 + committeeSize p + 32 * 6
  if fixed ≤ bs.size ∧ offsetAt bs 0 = fixed then
    (Ssz.Electra.Header.decode (extract bs fixed bs.size)).map fun h =>
      ⟨ofElectra h, readCommittee p (slice bs 4 (committeeSize p)), roots bs (4 + committeeSize p) 6⟩
  else none

def update (bs : ByteArray) : Option Update :=
  let fo := 4 + committeeSize p + 32 * 6
  let fixed := fo + 4 + 32 * 7 + aggregateSize p + 8
  let o₂ := offsetAt bs fo
  if fixed ≤ bs.size ∧ offsetAt bs 0 = fixed ∧ fixed ≤ o₂ ∧ o₂ ≤ bs.size then
    match Ssz.Electra.Header.decode (extract bs fixed o₂),
        Ssz.Electra.Header.decode (extract bs o₂ bs.size) with
    | some a, some f =>
      let g := fo + 4
      some ⟨ofElectra a, readCommittee p (slice bs 4 (committeeSize p)),
        roots bs (4 + committeeSize p) 6, ofElectra f, roots bs g 7,
        readAggregate p (slice bs (g + 32 * 7) (aggregateSize p)),
        u64 bs (g + 32 * 7 + aggregateSize p)⟩
    | _, _ => none
  else none

def finality (bs : ByteArray) : Option Update :=
  let fixed := 8 + 32 * 7 + aggregateSize p + 8
  let o₂ := offsetAt bs 4
  if fixed ≤ bs.size ∧ offsetAt bs 0 = fixed ∧ fixed ≤ o₂ ∧ o₂ ≤ bs.size then
    match Ssz.Electra.Header.decode (extract bs fixed o₂),
        Ssz.Electra.Header.decode (extract bs o₂ bs.size) with
    | some a, some f =>
      some ⟨ofElectra a, emptyCommittee p, zeroBranch 6, ofElectra f, roots bs 8 7,
        readAggregate p (slice bs (8 + 32 * 7) (aggregateSize p)),
        u64 bs (8 + 32 * 7 + aggregateSize p)⟩
    | _, _ => none
  else none

def optimistic (bs : ByteArray) : Option Update :=
  let fixed := 4 + aggregateSize p + 8
  if fixed ≤ bs.size ∧ offsetAt bs 0 = fixed then
    (Ssz.Electra.Header.decode (extract bs fixed bs.size)).map fun a =>
      ⟨ofElectra a, emptyCommittee p, zeroBranch 6, emptyElectra, zeroBranch 7,
        readAggregate p (slice bs 4 (aggregateSize p)), u64 bs (4 + aggregateSize p)⟩
  else none

end Electra

/-! ## Gloas -/

namespace Gloas

/-- A Gloas `LightClientHeader`'s size. -/
def headerSize : Nat := Ssz.Gloas.Header.size

def bootstrap (bs : ByteArray) : Option Bootstrap :=
  if bs.size = headerSize + committeeSize p + 32 * 11 then
    some ⟨ofGloas (Ssz.Gloas.Header.read (slice bs 0 headerSize)),
      readCommittee p (slice bs headerSize (committeeSize p)),
      roots bs (headerSize + committeeSize p) 11⟩
  else none

def update (bs : ByteArray) : Option Update :=
  let fa := headerSize + committeeSize p + 32 * 11
  let aa := fa + headerSize + 32 * 9
  if bs.size = aa + aggregateSize p + 8 then
    some ⟨ofGloas (Ssz.Gloas.Header.read (slice bs 0 headerSize)),
      readCommittee p (slice bs headerSize (committeeSize p)),
      roots bs (headerSize + committeeSize p) 11, ofGloas (Ssz.Gloas.Header.read (slice bs fa headerSize)),
      roots bs (fa + headerSize) 9, readAggregate p (slice bs aa (aggregateSize p)),
      u64 bs (aa + aggregateSize p)⟩
  else none

def finality (bs : ByteArray) : Option Update :=
  let aa := 2 * headerSize + 32 * 9
  if bs.size = aa + aggregateSize p + 8 then
    some ⟨ofGloas (Ssz.Gloas.Header.read (slice bs 0 headerSize)), emptyCommittee p, zeroBranch 11,
      ofGloas (Ssz.Gloas.Header.read (slice bs headerSize headerSize)), roots bs (2 * headerSize) 9,
      readAggregate p (slice bs aa (aggregateSize p)), u64 bs (aa + aggregateSize p)⟩
  else none

def optimistic (bs : ByteArray) : Option Update :=
  if bs.size = headerSize + aggregateSize p + 8 then
    some ⟨ofGloas (Ssz.Gloas.Header.read (slice bs 0 headerSize)), emptyCommittee p, zeroBranch 11,
      emptyGloas, zeroBranch 9, readAggregate p (slice bs headerSize (aggregateSize p)),
      u64 bs (headerSize + aggregateSize p)⟩
  else none

end Gloas

/-- The codec of a preset whose containers differ from mainnet's only in the committee's size. -/
def codec : Codec where
  bootstrap f bs := match f with
    | .gloas => Gloas.bootstrap p bs
    | _ => Electra.bootstrap p bs
  update k f bs := match f, k with
    | .gloas, .update => Gloas.update p bs
    | .gloas, .finality => Gloas.finality p bs
    | .gloas, .optimistic => Gloas.optimistic p bs
    | _, .update => Electra.update p bs
    | _, .finality => Electra.finality p bs
    | _, .optimistic => Electra.optimistic p bs

end LeanLight.Lc.Dev
