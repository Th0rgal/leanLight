import LeanLightTests.Bls.Util
import LeanLightTests.Bls.Vectors

/-!
# One interface over both BLS layers, and the vector suites run through it

`Layer` is what the vectors need of an implementation, in plain types; `Runtime` and
`Readable` fill it with the light client's `LeanLight.Bls` and with EthLib's code vendored in
`LeanLightProofs.Vendor.EthLib.Bls`. `vectors` runs every vector on one layer.
-/

namespace LeanLight.Tests.Bls

open Vectors

/-- An affine point of G2, `(x.c0, x.c1, y.c0, y.c1)`. -/
abbrev Pt2 := Nat × Nat × Nat × Nat

structure Layer where
  name : String
  /-- IRTF FastAggregateVerify over encodings. -/
  fav : List ByteArray → ByteArray → ByteArray → Bool
  /-- Ethereum's `eth_fast_aggregate_verify`. -/
  ethFav : List ByteArray → ByteArray → ByteArray → Bool
  /-- Ethereum's `eth_aggregate_pubkeys`, `none` when refused. -/
  ethAgg : List ByteArray → Option ByteArray
  /-- 48 bytes are a point of G1, the identity included. -/
  deserG1 : ByteArray → Bool
  /-- 96 bytes are a point of G2, the identity included. -/
  deserG2 : ByteArray → Bool
  /-- `[sk]·H(msg)`, compressed, Ethereum's DST; `none` for a key out of range. -/
  sign : Nat → ByteArray → Option ByteArray
  /-- `hash_to_G2(msg)` under a DST. -/
  h2g : ByteArray → ByteArray → Option Pt2
  /-- `hash_to_field(msg, 2)` under a DST. -/
  h2f : ByteArray → ByteArray → Option ((Nat × Nat) × (Nat × Nat))
  /-- `map_to_curve(u)`: SSWU, then the isogeny. -/
  map : Nat × Nat → Option Pt2
  sha256 : ByteArray → ByteArray

def pairOf (p : String × String) : Nat × Nat := (natOfHex p.1, natOfHex p.2)

/-- Every vector, on one layer. -/
def vectors (L : Layer) : IO Tally := do
  let mut t : Tally := {}
  for v in ethFav ++ csFav do
    t := t.add s!"{L.name} {v.name}"
      (L.ethFav (v.pubkeys.map unhex) (unhex v.message) (unhex v.signature) == v.output)
  for v in ethAgg ++ csAgg do
    t := t.add s!"{L.name} {v.name}" ((L.ethAgg (v.pubkeys.map unhex)).map hex == v.output)
  for v in blsFav ++ blsVerify do
    t := t.add s!"{L.name} {v.name}"
      (L.fav (v.pubkeys.map unhex) (unhex v.message) (unhex v.signature) == v.output)
  for v in blsG1 do
    t := t.add s!"{L.name} {v.name}" (L.deserG1 (unhex v.bytes) == v.output)
  for v in blsG2 do
    t := t.add s!"{L.name} {v.name}" (L.deserG2 (unhex v.bytes) == v.output)
  for v in blsSign do
    t := t.add s!"{L.name} {v.name}" ((L.sign (natOfHex v.privkey) (unhex v.message)).map hex == v.output)
  let dst := rfcDst.toUTF8
  for v in blsH2G do
    let (x0, x1) := pairOf v.px
    let (y0, y1) := pairOf v.py
    t := t.add s!"{L.name} {v.name}" (L.h2g v.msg.toUTF8 dst == some (x0, x1, y0, y1))
  for v in rfc do
    let m := v.msg.toUTF8
    let name := s!"{L.name} RFC 9380 J.10.1 msg \"{v.msg.take 12}\""
    t := t.add s!"{name} u" (L.h2f m dst == some (pairOf v.u0, pairOf v.u1))
    let (q0x0, q0x1) := pairOf v.q0x
    let (q0y0, q0y1) := pairOf v.q0y
    let (q1x0, q1x1) := pairOf v.q1x
    let (q1y0, q1y1) := pairOf v.q1y
    t := t.add s!"{name} Q0" (L.map (pairOf v.u0) == some (q0x0, q0x1, q0y0, q0y1))
    t := t.add s!"{name} Q1" (L.map (pairOf v.u1) == some (q1x0, q1x1, q1y0, q1y1))
    let (x0, x1) := pairOf v.px
    let (y0, y1) := pairOf v.py
    t := t.add s!"{name} P" (L.h2g m dst == some (x0, x1, y0, y1))
  -- FIPS 180-2's examples, and one block of 1000 bytes.
  t := t.add s!"{L.name} sha256('')" (hex (L.sha256 ByteArray.empty) ==
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
  t := t.add s!"{L.name} sha256('abc')" (hex (L.sha256 "abc".toUTF8) ==
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
  t := t.add s!"{L.name} sha256(448 bits)" (hex (L.sha256
    "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8) ==
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1")
  t := t.add s!"{L.name} sha256(896 bits)" (hex (L.sha256
    "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu".toUTF8) ==
    "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1")
  return t

end LeanLight.Tests.Bls
