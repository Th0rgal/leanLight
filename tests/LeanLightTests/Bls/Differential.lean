import LeanLightTests.Bls.Runtime
import LeanLightTests.Bls.Readable

/-!
# The two layers against each other

On inputs no vector has, `LeanLight.Bls` (the runtime layer) and EthLib's readable layer must give
the same answers:

* **mutations**: every byte of a valid signature, of a valid aggregate's keys and of its
  message, one bit flipped, refused by the runtime layer; a sample refused by EthLib's too;
* **hash_to_G2** on messages of several lengths and on a DST longer than 255 bytes (RFC 9380
  §5.3.3), equal; `clear_cofactor` as `[h_eff]P` equal to EthLib's Appendix G.3 method;
* **decompression** of keys and signatures near valid ones, accepted alike and to one point;
* **the final exponentiation's cube**: `finalExp (millerLoop ps)`, the runtime's, equals the
  cube of EthLib's naive `finalExponentiation` of its `pairingCheck` accumulator over the same
  pairs (`docs/spec-16-light-client.md`, "Proved, checked by vectors, trusted"), on pairs whose
  product is one and on pairs whose product is not.
-/

namespace LeanLight.Tests.Bls

/-- `b` with bit `bit` of byte `i` flipped. -/
def flip (b : ByteArray) (i bit : Nat) : ByteArray :=
  if h : i < b.size then b.set i (b[i] ^^^ ((1 : UInt8) <<< bit.toUInt8)) h else b

namespace Conv

def fp2 (a : EthLib.Cryptography.Bls.Fp2) : LeanLight.Lc.Bls.Fp2 := ⟨a.c0.val, a.c1.val⟩
def fp6 (a : EthLib.Cryptography.Bls.Fp6) : LeanLight.Lc.Bls.Fp6 := ⟨fp2 a.c0, fp2 a.c1, fp2 a.c2⟩
def fp12 (a : EthLib.Cryptography.Bls.Fp12) : LeanLight.Lc.Bls.Fp12 := ⟨fp6 a.c0, fp6 a.c1⟩

def g1 (p : LeanLight.Lc.Bls.G1A) : EthLib.Cryptography.Bls.G1 :=
  ⟨EthLib.Cryptography.Bls.Fp.ofNat p.x, EthLib.Cryptography.Bls.Fp.ofNat p.y,
   EthLib.Cryptography.Bls.Fp.one⟩

def efp2 (a : LeanLight.Lc.Bls.Fp2) : EthLib.Cryptography.Bls.Fp2 :=
  ⟨EthLib.Cryptography.Bls.Fp.ofNat a.c0, EthLib.Cryptography.Bls.Fp.ofNat a.c1⟩

def g2 (p : LeanLight.Lc.Bls.G2A) : EthLib.Cryptography.Bls.G2 :=
  ⟨efp2 p.x, efp2 p.y, EthLib.Cryptography.Bls.Fp2.one⟩

end Conv

/-- EthLib's `pairingCheck` accumulator over `ps`, before its final exponentiation. -/
def ethAcc (ps : List (LeanLight.Lc.Bls.G1A × LeanLight.Lc.Bls.G2A)) : EthLib.Cryptography.Bls.Fp12 :=
  ps.foldl (fun acc pq =>
    let f := EthLib.Cryptography.Bls.millerLoop EthLib.Cryptography.Bls.blsX
      (EthLib.Cryptography.Bls.Embedded.ofG2 (Conv.g2 pq.2))
      (EthLib.Cryptography.Bls.Embedded.ofG1 (Conv.g1 pq.1))
    acc * f.conjugate) EthLib.Cryptography.Bls.Fp12.one

def differential (z : Nat) : IO Tally := do
  let mut t : Tally := {}
  -- Mutations of the first two valid eth_fast_aggregate_verify vectors with keys (valid_0, valid_1).
  for v in (Vectors.ethFav.filter fun v => v.output && !v.pubkeys.isEmpty).take 2 do
    let pks := v.pubkeys.map unhex
    let msg := unhex v.message
    let sig := unhex v.signature
    let mut sigOk := true
    for i in [0:sig.size] do
      sigOk := sigOk && !runtime.fav pks msg (flip sig i ((i + z) % 8))
    for b in [0:8] do
      sigOk := sigOk && !runtime.fav pks msg (flip sig 0 b)
    t := t.add s!"runtime refuses {sig.size + 8} one-bit mutations of {v.name}'s signature" sigOk
    let mut keyOk := true
    for k in [0:pks.length] do
      let pk := pks[k]?.getD ByteArray.empty
      for i in [0:pk.size] do
        keyOk := keyOk && !runtime.fav (pks.set k (flip pk i ((i + 3) % 8))) msg sig
    t := t.add s!"runtime refuses {48 * pks.length} one-bit mutations of {v.name}'s keys" keyOk
    let mut msgOk := true
    for i in [0:msg.size] do
      msgOk := msgOk && !runtime.fav pks (flip msg i (i % 8)) sig
    t := t.add s!"runtime refuses {msg.size} one-bit mutations of {v.name}'s message" msgOk
    let sample := [flip sig 0 7, flip sig 0 6, flip sig 0 5, flip sig 47 0, flip sig 95 1]
    t := t.add s!"readable refuses 5 mutations of {v.name}'s signature"
      (sample.all fun s => !readable.fav pks msg s)
    t := t.add s!"readable refuses a mutated key and a mutated message of {v.name}"
      (!readable.fav (pks.set 0 (flip (pks[0]?.getD ByteArray.empty) 20 2)) msg sig &&
        !readable.fav pks (flip msg 31 0) sig)
  -- hash_to_G2, both layers, Ethereum's DST, and a DST longer than 255 bytes.
  let mut h2gOk := true
  let mut n := 0
  for len in [0, 1, 31, 32, 33, 64, 100, 255, 256, 300] do
    let m := ByteArray.mk ((Array.range len).map fun i => (i * 7 + z).toUInt8)
    for dst in [LeanLight.Lc.Bls.ethDst, ByteArray.mk ((Array.range 300).map fun i => (i + 1).toUInt8)] do
      n := n + 1
      let a := runtime.h2g m dst
      h2gOk := h2gOk && a.isSome && a == readable.h2g m dst
  t := t.add s!"hash_to_G2 equal on {n} messages, two DSTs" h2gOk
  -- clear_cofactor: [h_eff]P, both layers, against EthLib's G.3.
  let mut cofOk := true
  for k in [1:6] do
    let u : LeanLight.Lc.Bls.Fp2 := ⟨k * 0x1234567 + z, k * 0x89abcdef⟩
    match LeanLight.Lc.Bls.H2C.sswu? u with
    | none => cofOk := false
    | some q =>
      let r := LeanLight.Lc.Bls.H2C.isoMap q
      let rt := (LeanLight.Lc.Bls.H2C.clearCofactor r).toAffine?.map g2Pt
      let ra := (r.toAffine?.map Conv.g2).getD EthLib.Cryptography.Bls.G2.zero
      cofOk := cofOk && rt.isSome && rt == ethPt2 (EthLib.Cryptography.Bls.HashToCurve.clearCofactor ra)
        && rt == ethPt2 (EthLib.Cryptography.Bls.HashToCurve.clearCofactorG3 ra)
  t := t.add "clear_cofactor: [h_eff]P (both layers) = EthLib's G.3 on 5 points" cofOk
  -- Decompression near valid encodings.
  let mut decOk := true
  let mut nDec := 0
  for k in [1:25] do
    let p := (LeanLight.Lc.Bls.G1J.mulA LeanLight.Lc.Bls.g1Gen (k + z)).compress
    let q := (LeanLight.Lc.Bls.G2J.mulA LeanLight.Lc.Bls.g2Gen (k + z)).compress
    let ps := [p, flip p 0 5, flip p 47 0, flip p 47 1, flip p 20 3, flip p 0 6]
    let qs := [q, flip q 0 5, flip q 95 0, flip q 95 1, flip q 20 3, flip q 0 6]
    for (p', q') in ps.zip qs do
      let a := LeanLight.Lc.Bls.keyValidate? p'
      let b := EthLib.Cryptography.Bls.G1.keyValidate p'
      let pt := match EthLib.Cryptography.Bls.G1.uncompress p' with
        | .ok e => some (e.x.val, e.y.val)
        | .error _ => none
      decOk := decOk && a.isSome == b.isOk && (a.isNone || a.map (fun x => (x.x, x.y)) == pt)
      let c := LeanLight.Lc.Bls.sigValidate? q'
      let d := match EthLib.Cryptography.Bls.G2.uncompress q' with
        | .ok e => !e.isInfinity && EthLib.Cryptography.Bls.G2.inSubgroup e
        | .error _ => false
      decOk := decOk && c.isSome == d
      nDec := nDec + 2
  t := t.add s!"KeyValidate and the signature's checks agree on {nDec} encodings" decOk
  -- The cube: finalExp (millerLoop ps) = (EthLib's finalExponentiation of its accumulator)^3.
  let v := Vectors.ethFav.filter (fun v => v.output && !v.pubkeys.isEmpty) |>.headD
    { name := "", pubkeys := [], message := "", signature := "", output := false }
  let pk := (LeanLight.Lc.Bls.keyValidate? (unhex (v.pubkeys.headD ""))).getD LeanLight.Lc.Bls.g1Gen
  let sg := (LeanLight.Lc.Bls.sigValidate? (unhex v.signature)).getD LeanLight.Lc.Bls.g2Gen
  let hm := (LeanLight.Lc.Bls.H2C.hashToG2? (unhex v.message) LeanLight.Lc.Bls.ethDst).getD LeanLight.Lc.Bls.g2Gen
  let cases : List (String × List (LeanLight.Lc.Bls.G1A × LeanLight.Lc.Bls.G2A)) :=
    [("e(g1, g2)", [(LeanLight.Lc.Bls.g1Gen, LeanLight.Lc.Bls.g2Gen)]),
     (s!"{v.name}'s check, which holds", [(LeanLight.Lc.Bls.g1Gen, sg), (pk.neg, hm)]),
     (s!"{v.name}'s check under -g1, which fails", [(LeanLight.Lc.Bls.g1Gen.neg, sg), (pk.neg, hm)])]
  for (name, ps) in cases do
    let fast := LeanLight.Lc.Bls.finalExp (LeanLight.Lc.Bls.millerLoop ps)
    let e := EthLib.Cryptography.Bls.finalExponentiation (ethAcc ps)
    t := t.add s!"finalExp (millerLoop ps) = (EthLib's final exponentiation)^3: {name}"
      (fast.eq (Conv.fp12 (e * e * e)))
    t := t.add s!"pairingCheck agrees with EthLib's: {name}"
      (LeanLight.Lc.Bls.pairingCheck ps == EthLib.Cryptography.Bls.pairingCheck
        ((ps.map fun pq => (Conv.g1 pq.1, Conv.g2 pq.2)).toArray))
  return t

end LeanLight.Tests.Bls
