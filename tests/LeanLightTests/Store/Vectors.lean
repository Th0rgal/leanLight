import LeanLightTests.Store.Util

/-!
# The minimal preset's `sync` and `update_ranking` vectors

consensus-specs v1.7.0-beta.4's `light_client/sync` and `light_client/update_ranking` for
Electra, Fulu and Gloas (`vectors/light_client`, its README), run on `LeanLight.Store` with the
minimal preset's decoders (`LeanLightDev`), under the rules of `docs/spec-16-light-client.md`,
"Testing":

* each step's update is decoded as the fork its digest names, which must be the fork of its
  attested slot (`Codec.decodeUpdate`), and must be accepted;
* after each step, `slot`, `beacon_root` and `execution_root` of the finalized header are
  compared, and the optimistic header's against the anchor or the finalized header, whichever is
  newer (lkd has no optimistic header; every step has full participation);
* now is `slotTime(current_slot)`;
* a `force_update` whose checks differ from the previous step's forces an update, which lkd
  never does (N6): it and the rest of its case are reported unsupported, not failed; one whose
  checks are unchanged is a no-op;
* `upgrade_store` changes nothing: the store keeps each header in the form it was validated in,
  and `get_lc_execution_root` is the same for an Electra header and its upgrade.

`update_ranking`: the updates are listed best first, so `isBetter` must prefer each to every
later one, and never a later one to an earlier one; and on every pair, `isBetter` (the
lexicographic order on `Store.rank` that runs) must agree with `isBetterSpec`, the
specification's `is_better_update` transcribed as written.
-/

namespace LeanLightTests.Store

open LeanLight.Lc
open LeanLight.Lc.Store (Header Update Exec)

/-- `get_lc_execution_root`: an Electra or Fulu header's payload root; a Gloas header's
`execution_block_hash` from the Gloas fork on; before it, the payload root the normalized
branch climbs to from the block hash (gindex 44 in Deneb's payload header). -/
def executionRoot (c : Forks.Chain) (h : Header) : ByteArray :=
  match h.exec with
  | .payload e => e.root
  | .blockHash b =>
    if c.gloasAt h.beacon.slot then b
    else if h.beacon.slot = 0 then Codec.emptyPayload.root
    else Ssz.climb 44 h.branch (h.branch.size - 9) 5 0 b

/-- `slot beacon_root execution_root` of a header. -/
def summary (c : Forks.Chain) (h : Header) : List String :=
  [toString h.beacon.slot, hex h.root, hex (executionRoot c h)]

/-- The store's finalized header, and its optimistic header's stand-in: the anchor or the
finalized header, whichever is newer. -/
def observed (c : Forks.Chain) (s : Store.Store) : List String :=
  let opt := match s.anchor with
    | some a => if s.finalized.beacon.slot < a.header.beacon.slot then a.header else s.finalized
    | none => s.finalized
  summary c s.finalized ++ summary c opt

/-- One `sync` case. -/
def runSync (t : Tally) (dir : System.FilePath) (name : String) : IO Tally := do
  let mt := ((← IO.FS.readFile (dir / "meta.txt")).splitOn " ").map (·.trimAscii.toString)
  let gvr := unhex (mt[0]?.getD "")
  let trusted := unhex (mt[1]?.getD "")
  let c := chainOf (← IO.FS.readFile (dir / "config.txt")) gvr
  let steps := linesOf (← IO.FS.readFile (dir / "steps.txt"))
  let mut t := t
  let bs ← IO.FS.readBinFile (dir / "bootstrap.ssz")
  let some b := Codec.decodeBootstrap codec c (.digest (unhex (mt[2]?.getD ""))) bs
    | return t.check false s!"{name}: the bootstrap does not decode as its digest's fork"
  let first := natOf ((steps.head?.bind (·[3]?)).getD "0")
  let some s0 := Store.bootstrap c trusted (c.slotTime b.header.beacon.slot) b
    | return t.check false s!"{name}: bootstrap refused"
  t := t.check true s!"{name}: bootstrap"
  let _ := first
  let mut s := s0
  let mut previous : List String := observed c s
  let mut i := 0
  for step in steps do
    i := i + 1
    match step with
    | "process_update" :: digest :: file :: slot :: checks =>
      let ub ← IO.FS.readBinFile (dir / (file ++ ".ssz"))
      match Codec.decodeUpdate codec c .update (.digest (unhex digest)) ub with
      | none =>
        t := t.check false s!"{name} step {i}: the update does not decode as its digest's fork"
        return t
      | some u =>
        let (s', v) := Store.receive c s (c.slotTime (natOf slot)) u
        s := s'
        let ok := match v with | .accepted _ _ => true | _ => false
        t := t.check ok s!"{name} step {i}: update not accepted"
        let got := observed c s
        t := t.check (got == checks) s!"{name} step {i}: store {got}, expected {checks}"
        previous := checks
    | "force_update" :: _ :: checks =>
      if checks == previous then
        t := t.check (observed c s == checks) s!"{name} step {i}: a no-op force_update"
      else
        t := t.skip s!"{name}: steps {i} to {steps.length}, from an effective force_update (N6)"
        return t
    | "upgrade_store" :: _ :: checks =>
      t := t.check (observed c s == checks) s!"{name} step {i}: upgrade_store: store {observed c s}, expected {checks}"
      previous := checks
    | _ => t := t.check false s!"{name} step {i}: unknown step"
  return t

/-- `is_better_update(new, old)` as the specification writes it
(`altair/light-client/sync-protocol.md`), transcribed for the tests: `Store.isBetter`, the
lexicographic order on `Store.rank` that runs, must agree with it on every pair. -/
def isBetterSpec (c : Forks.Chain) (new old : Update) : Bool :=
  let p := c.preset
  let nn := new.signers p
  let on := old.signers p
  let nsm := Store.supermajority p nn
  let osm := Store.supermajority p on
  if nsm != osm then nsm
  else if !nsm && nn != on then decide (nn > on)
  else
    let nrel := new.isSyncCommitteeUpdate && c.periodAt new.slot == c.periodAt new.signatureSlot
    let orel := old.isSyncCommitteeUpdate && c.periodAt old.slot == c.periodAt old.signatureSlot
    if nrel != orel then nrel
    else
      let nfin := new.isFinalityUpdate
      let ofin := old.isFinalityUpdate
      if nfin != ofin then nfin
      else
        let nscf := c.periodAt new.finalized.beacon.slot == c.periodAt new.slot
        let oscf := c.periodAt old.finalized.beacon.slot == c.periodAt old.slot
        if nfin && nscf != oscf then nscf
        else if nn != on then decide (nn > on)
        else if new.slot != old.slot then decide (new.slot < old.slot)
        else decide (new.signatureSlot < old.signatureSlot)

/-- The `update_ranking` case of a fork. -/
def runRanking (t : Tally) (dir : System.FilePath) (fork : Forks.ForkName) (name : String) :
    IO Tally := do
  let count := natOf ((← IO.FS.readFile (dir / "meta.txt")).trimAscii.toString)
  let forks : List Forks.Fork := match fork with
    | .electra => [⟨.electra, 0, unhex "05000001"⟩]
    | .fulu => [⟨.electra, 0, unhex "05000001"⟩, ⟨.fulu, 0, unhex "06000001"⟩]
    | .gloas => [⟨.electra, 0, unhex "05000001"⟩, ⟨.fulu, 0, unhex "06000001"⟩,
        ⟨.gloas, 0, unhex "07000001"⟩]
  let c : Forks.Chain := { chainOf "" ⟨Array.replicate 32 0⟩ with forks }
  let mut us : Array Update := #[]
  let mut t := t
  for i in List.range count do
    let bs ← IO.FS.readBinFile (dir / s!"updates_{i}.ssz")
    match Codec.decodeUpdate codec c .update (.name fork) bs with
    | some u => us := us.push u
    | none => t := t.check false s!"{name}: updates_{i} does not decode"
  let mut wrong := 0
  let mut differ := 0
  for hi : i in [0:us.size] do
    for hj : j in [0:us.size] do
      let ui := us[i]'hi.2.1
      let uj := us[j]'hj.2.1
      if i < j && !(Store.isBetter c ui uj && !Store.isBetter c uj ui) then wrong := wrong + 1
      if i == j && Store.isBetter c ui uj then wrong := wrong + 1
      if Store.isBetter c ui uj != isBetterSpec c ui uj then differ := differ + 1
  t := t.check (wrong == 0) s!"{name}: {wrong} pairs out of order"
  t := t.check (differ == 0) s!"{name}: isBetter differs from the specification's on {differ} pairs"
  return t

def syncCases : List (String × String) :=
  [ ("electra", "advance_finality_without_sync_committee"), ("electra", "gloas_store_with_legacy_data"),
    ("electra", "light_client_sync"), ("electra", "light_client_sync_no_force_update"),
    ("electra", "supply_sync_committee_from_past_update"),
    ("fulu", "advance_finality_without_sync_committee"), ("fulu", "gloas_fork"),
    ("fulu", "gloas_store_with_legacy_data"), ("fulu", "light_client_sync"),
    ("fulu", "light_client_sync_no_force_update"), ("fulu", "supply_sync_committee_from_past_update"),
    ("gloas", "advance_finality_without_sync_committee"), ("gloas", "light_client_sync"),
    ("gloas", "light_client_sync_no_force_update"), ("gloas", "supply_sync_committee_from_past_update") ]

/-- Every vector case, into the tally. -/
def runVectors (root : System.FilePath) (t : Tally) : IO Tally := do
  let mut t := t
  for (fork, case) in syncCases do
    t ← runSync t (root / fork / "sync" / case) s!"{fork}/sync/{case}"
  for (fork, f) in [("electra", Forks.ForkName.electra), ("fulu", .fulu), ("gloas", .gloas)] do
    t ← runRanking t (root / fork / "update_ranking") f s!"{fork}/update_ranking"
  return t

end LeanLightTests.Store
