import LeanLight.Bls.Compress
import LeanLight.Bls.HashToG2
import LeanLight.Bls.Pairing

/-!
# BLS12-381: FastAggregateVerify, the light client's entry

What the light client's store calls (leanKohakuDesktop's `spec/16-light-client.md`, "Cryptography in Lean"):

* `keyValidate?` (`LeanLight.Bls.Compress`), once per committee key, when a committee is taken in;
* `fastAggregateVerify pks msg sig`, per update, over the keys of the participants, each one
  `keyValidate?` returned, the message the signing root and `sig` the signature's 96 bytes.

`fastAggregateVerify` is IRTF BLS's FastAggregateVerify (draft-irtf-cfrg-bls-signature-05
§3.3.4) for Ethereum's ciphersuite `BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_`, in CoreVerify's
arrangement as EthLib's `coreVerify` has it, `e(g₁, σ)·e(−agg, H(m)) = 1`:

1. the aggregate `agg` is the sum of the participants' keys (not the committee's
   `aggregate_pubkey` minus the absent, helios's shortcut, which rests on an unchecked
   equation), and is refused when it is the identity, as CoreVerify's KeyValidate of it would
   (so no key at all is refused too);
2. the signature passes `sigValidate?`: on the twist, not the identity, `[r]σ = O`;
3. `H(m)` is `hash_to_G2(m)` under Ethereum's DST, refused if SSWU refuses or it is the
   identity (`LeanLight.Bls.HashToG2`);
4. one Miller loop over the two pairs and one final exponentiation, which must give one.

EthLib's `ethFastAggregateVerify` differs from this on some inputs. It accepts an identity
signature into the pairing, and it skips identity pairs, which here are refused: when `H(m)` is
the identity and the signature is the identity's encoding, EthLib skips both pairs and accepts,
where this refuses (found in LC4b; `H(m) = O` needs a hash-to-curve output at the identity); and
when the signature is the identity's encoding it accepts exactly when `e(Σ pk, H(m)) = 1`, which
the pairing's non-degeneracy excludes for `H(m)` in G2. EthLib's special case for an empty key
list (true when the signature is the identity's encoding) is Ethereum's
`eth_fast_aggregate_verify`, which the light client does not call: the sync protocol's
`validate_light_client_update` calls FastAggregateVerify, after requiring at least one
participant. 25c (LC4b) proves `fastAggregateVerify` true exactly when the key sum is not the
identity, the signature decodes to `σ`, `H(m) = hash_to_G2(m)` and `e(g₁, σ) = e(Σ pk, H(m))`,
for any `e` additive in its first argument, given H_vec's pairing hypothesis; and (LC4b's rest)
`fastAggregateVerifyBytes` equal to EthLib's `fastAggregateVerify` on every input where `H(m)` is
not the identity and the signature is not the identity's encoding, given H_vec's final
exponentiation equation (`fastAggregateVerifyBytes_eq_eth`), the identity's encoding
characterized as above (`fastAggregateVerify_eth_identitySig`).
-/

namespace LeanLight.Lc.Bls

/-- Ethereum's ciphersuite's domain separation tag. -/
def ethDst : ByteArray := "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_".toUTF8

/-- The sum of `pks`, affine; `none` when it is the identity (no key included). -/
def aggregate? (pks : Array G1A) : Option G1A :=
  (pks.foldl (fun acc p => acc.addA p) G1J.inf).toAffine?

/-- FastAggregateVerify over keys `keyValidate?` returned: the participants' keys `pks`, the
message `msg` (the signing root) and the signature's 96 bytes `sig`. -/
def fastAggregateVerify (pks : Array G1A) (msg sig : ByteArray) : Bool :=
  match aggregate? pks with
  | none => false
  | some agg =>
    match sigValidate? sig with
    | none => false
    | some s =>
      match H2C.hashToG2? msg ethDst with
      | none => false
      | some h => pairingCheck [(g1Gen, s), (agg.neg, h)]

/-- FastAggregateVerify over encodings, as IRTF BLS states it: every key `keyValidate?`
accepts, then `fastAggregateVerify`. -/
def fastAggregateVerifyBytes (pks : Array ByteArray) (msg sig : ByteArray) : Bool :=
  match pks.mapM keyValidate? with
  | some keys => fastAggregateVerify keys msg sig
  | none => false

end LeanLight.Lc.Bls
