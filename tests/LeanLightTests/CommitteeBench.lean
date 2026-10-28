import LeanLight

/-!
`lake exe leanlight-committee-bench [bootstrap.ssz]`: where taking in a sync committee spends its
time, on a real mainnet bootstrap: decoding, the committee's root, decompression (the square root),
the subgroup check by `[r]P` and by Scott's endomorphism test, and `Committee.ofSync` whole.
-/

open LeanLight.Lc LeanLight.Lc.Bls

def timeIt {α} (label : String) (reps : Nat) (f : Unit → α) (fmt : α → String) : IO α := do
  let t0 ← IO.monoNanosNow
  let mut a := f ()
  for _ in [1:reps] do a := f ()
  let t1 ← IO.monoNanosNow
  IO.println s!"{label}: {(t1 - t0) / reps / 1000000}.{(t1 - t0) / reps / 1000 % 1000} ms  [{fmt a}]"
  return a

def main (args : List String) : IO UInt32 := do
  let path := args.headD "vectors/bench-bootstrap.ssz"
  let bs ← IO.FS.readBinFile path
  let some b ← timeIt "decode bootstrap" 1 (fun _ => Codec.mainnetBootstrap .fulu bs) (fun o => toString o.isSome)
    | IO.println "does not decode"; return 1
  let keys := b.committee.pubkeys
  let _ ← timeIt "committee root" 1 (fun _ => Store.committeeRoot Forks.mainnetPreset b.committee) (fun r => toString r.size)
  let pts ← timeIt "decompress 512 (sqrt)" 1 (fun _ => keys.filterMap g1Decompress?) (fun a => toString a.size)
  let _ ← timeIt "subgroup [r]P x512" 1 (fun _ => pts.all (·.inSubgroup)) toString
  let _ ← timeIt "subgroup Scott x512" 1 (fun _ => pts.all (·.inSubgroupScott)) toString
  let _ ← timeIt "Committee.ofSync whole" 1 (fun _ => Store.Committee.ofSync Forks.mainnetPreset b.committee) (fun o => toString o.isSome)
  return 0
