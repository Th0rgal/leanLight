import LeanLight

/-!
`lake exe leanlight-committee-bench [bootstrap.ssz]`: where taking in a sync committee spends its
time, on a real mainnet bootstrap: decoding, the committee's root, decompression (the square root),
the subgroup check by `[r]P` and by Scott's endomorphism test (which the store no longer runs), and
`Committee.ofSync` whole; then one signature's steps.
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
  let some com ← timeIt "Committee.ofSync whole" 1 (fun _ => Store.Committee.ofSync Forks.mainnetPreset b.committee) (fun o => toString o.isSome)
    | IO.println "committee refused"; return 1
  -- a finality update of the same period, signed by that committee
  let fs ← IO.FS.readBinFile (args.getD 1 "vectors/bench-finality.ssz")
  let some u := Codec.mainnetUpdate .finality .fulu fs | IO.println "update does not decode"; return 1
  let c := Forks.mainnet
  let some v := c.signatureVersion u.signatureSlot | return 1
  let msg := Forks.signingRoot u.attested.root (Forks.computeDomain Forks.domainSyncCommittee v c.genesisValidatorsRoot)
  let parts ← timeIt "participants (sqrt each)" 1 (fun _ => (Store.participants com.pubkeys u.aggregate.bits).filterMap g1Decompress?) (fun a => toString a.size)
  let _ ← timeIt "aggregate (G1 adds)" 1 (fun _ => aggregate? parts) (fun o => toString o.isSome)
  let _ ← timeIt "signersSum? (readable)" 1 (fun _ => Store.signersSum? com u.aggregate.bits) (fun o => toString o.isSome)
  let _ ← timeIt "signersKey? (aggregate less absent)" 1 (fun _ => Store.signersKey? com u.aggregate.bits) (fun o => toString o.isSome)
  let _ ← timeIt "sigValidate? (G2 decompress + ψ)" 1 (fun _ => sigValidate? u.aggregate.signature) (fun o => toString o.isSome)
  let _ ← timeIt "g2Decompress? + [r]Q (slow check)" 1 (fun _ => (g2Decompress? u.aggregate.signature).filter (·.inSubgroup)) (fun o => toString o.isSome)
  let _ ← timeIt "g2Decompress? only" 1 (fun _ => g2Decompress? u.aggregate.signature) (fun o => toString o.isSome)
  let some h ← timeIt "hashToG2" 1 (fun _ => H2C.hashToG2? msg ethDst) (fun o => toString o.isSome) | return 1
  let some s := sigValidate? u.aggregate.signature | return 1
  let some agg := aggregate? parts | return 1
  let _ ← timeIt "pairingCheck (2 Miller loops + final exp)" 1 (fun _ => pairingCheck [(g1Gen, s), (agg.neg, h)]) toString
  let _ ← timeIt "verifySignature whole" 1 (fun _ => Store.verifySignature c com u) toString
  return 0
