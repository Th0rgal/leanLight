# leanLight

An Ethereum consensus light client written in Lean 4, with machine-checked proofs about the code
that runs. It follows mainnet or Sepolia from a checkpoint by the sync protocol (BLS12-381
signatures of the sync committee, SSZ Merkle branches), then answers execution-layer reads
(balances, nonces, code, storage) by checking `eth_getProof` proofs against the state root of a
block its own verified beacon header names. Nothing an RPC endpoint says is believed until the
light client has checked it.

The code was extracted from [leanKohakuDesktop](https://github.com/nconsigny/leanKohakuDesktop)'s
light client (commit `8bddee0e`), where it runs sandboxed inside the wallet. Here it stands
alone: a library, its proofs, its tests and a command-line client.

## What is in it

| Directory | What | Imports |
|---|---|---|
| `LeanLight/` | The light client: SHA-256, Keccak-256, RLP, SSZ (decoding, `hash_tree_root`, branches), BLS12-381 (fields to `Fp12`, G1, G2, hash-to-G2, the pairing, FastAggregateVerify), the chain table (mainnet, Sepolia, Electra to Gloas), the sync protocol's store, execution-layer headers, Merkle-Patricia proofs, the reads anchored on a verified header, and the inclusion verdict for transactions and receipts | Lean core only |
| `proofs/` | Theorems about `LeanLight`'s definitions, against readable specifications: the vendored [ssz-specs](https://github.com/ethereum/ssz-specs) (MIT), [EthLib](https://github.com/ethereum/EthLib)'s BLS12-381 (CC0) and [VCVio](https://github.com/Verified-zkEVM/VCVio)'s SHA-2 (Apache-2.0), with Mathlib's elliptic-curve group law | Mathlib |
| `tests/` | consensus-specs' light-client and SSZ vectors, BLS vectors and a differential test against EthLib's readable BLS, a committee benchmark | `LeanLight` |
| `Main.lean`, `LeanLightCli/` | `leanlight`, the command-line client (HTTP through `curl`) | `LeanLight` |
| `bench/` | The comparison with [Helios](https://github.com/a16z/helios) on the same endpoints, and its results | Python 3 |
| `scripts/` | The axiom audit and the kernel replay | |

What the proofs cover, in brief (the statements are in the files):

- **BLS12-381**: the runtime's field and curve arithmetic is Mathlib's group law
  (`Bls/Curves.lean`, `Bls/Jacobian.lean`); decompression is sound and canonical; KeyValidate
  accepts exactly the compressions of the points of G1 other than the identity, and equals
  EthLib's (`Bls/Decompress.lean`, `Bls/Roundtrip.lean`, `Bls/FavEth.lean`); KeyValidate runs
  Scott's subgroup test, proved sound (`Bls/Scott.lean`); hash-to-G2 equals EthLib's
  (`Bls/HashEth.lean`); FastAggregateVerify equals EthLib's when the message does not hash to
  the identity and the signature is not the identity's encoding, given the Miller-loop
  hypothesis below (`fastAggregateVerifyBytes_eq_eth`). That the pairing is bilinear and
  non-degenerate, and that the fast final exponentiation computes the cube of the naive one,
  are named hypotheses checked by the vectors, not proved (`H_vec` in the comments).
- **SSZ**: the decoders are canonical and agree with ssz-specs; `hash_tree_root` of each light-client
  container is ssz-specs'; a branch verifies exactly when the leaf is in the tree (`Ssz*.lean`).
- **The store**: bootstrap binds the checkpoint; an update is accepted only after every check of
  the sync protocol, BLS included; conflicts halt the store; the age bound and the clock
  (`Store.lean`, `Forks.lean`).
- **Reads**: an EL header is bound to the verified beacon header only when its RLP hashes to the
  execution block hash; an account or storage value is what the Merkle-Patricia trie under that
  header's state root holds, short of a Keccak-256 collision on bytes the theorem names
  (`Anchor.lean`, `Trie.lean`, `Spec/MptTrie.lean`, `Inclusion.lean`).

`scripts/check-axioms.sh` audits every constant of `LeanLight` and `LeanLightProofs` (about
6,100, 2,865 of them theorems): each may rest only on `propext`, `Classical.choice` and
`Quot.sound`, so no `sorry` and no `native_decide`. `scripts/check-kernel.sh` replays every
module through Lean's kernel.

## Building

Lean 4.35.0 (`elan` picks it from `lean-toolchain`) and, for the client, `curl`.

```sh
lake build                               # the library and leanlight: .lake/build/bin/leanlight
(cd tests && lake build && ./.lake/build/bin/leanlight-store-test \
  && ./.lake/build/bin/leanlight-ssz-test && ./.lake/build/bin/leanlight-bls-test --quick)
(cd proofs && lake exe cache get && lake build)   # the proofs, with Mathlib's cache
scripts/check-axioms.sh && scripts/check-kernel.sh
```

## The client

```sh
leanlight [--network mainnet|sepolia] --consensus-rpc URL --execution-rpc URL \
          [--checkpoint 0xROOT] [--json] [-v] COMMAND
```

| Command | Prints |
|---|---|
| `sync` | the finalized and anchored slots, what was fetched and how long checking took |
| `block-number` | the anchored execution block's number |
| `balance ADDR`, `nonce ADDR` | the account's, from its proof |
| `code ADDR` | the proved code hash, the code accepted only if it hashes to it |
| `storage ADDR SLOT...` | storage words, from their proofs |
| `queries FILE` | one sync, then every line of `FILE` (`bench/mainnet.queries`) at one block |

The beacon node must serve the light-client API in SSZ (Nimbus and Lodestar do; publicnode's
beacon API serves JSON only). Without `--checkpoint`, the node's finalized root is taken on
trust, as Helios does without one; give a checkpoint you got elsewhere to remove that trust.
Example:

```sh
leanlight --consensus-rpc http://testing.mainnet.beacon-api.nimbus.team \
  --execution-rpc https://ethereum-rpc.publicnode.com \
  balance 0xd8dA6BF26964aF9D7eEd9e03E53415D37aA96045
```

The client syncs in one round trip (bootstrap, the current period's update, the finality and
optimistic updates fetched together; older periods after) and fetches a whole set of reads in
one JSON-RPC batch. Every value it prints comes out of `LeanLight`'s checked readers, never out
of the JSON. Committee keys are validated in parallel on every core.

## Against Helios

`bench/compare.py` starts Helios (`a16z/helios` `2af9b41`) and `leanlight` from the same
checkpoint on the same consensus and execution endpoints, takes each read at leanLight's anchored
block from both and from the endpoint itself, and compares. Results of 2026-10-29 on mainnet
(32-core machine; `bench/results/2026-10-29/`):

| | Helios | leanLight |
|---|---|---|
| Sync from a fresh checkpoint | 0.56–2.44 s | 0.26–0.69 s (of which checking about 0.1 s) |
| Sync from a checkpoint 6 sync periods old | 0.82–2.29 s | 1.10–4.48 s (checking 0.4–0.6 s; the rest the beacon node) |
| 14 reads (balances, nonces, code, storage) | 0.40–1.73 s, one call each | 0.25–0.39 s, one batch |
| Memory (RSS) | 22–24 MB | 22–24 MB |
| Binary | 25 MB | 6.4 MB |

Every value leanLight returned equalled the endpoint's at its block, and Helios's wherever Helios
answered at that block. With Lodestar's public beacon node as its source, Helios failed to become
ready within 120 s in two rounds out of three; leanLight synced from it in under 0.4 s.

On one core, a sync committee's 512 keys take 0.16 s to validate (decompression and Scott's
test); a signature check takes 17 ms (hash-to-G2 6 ms, the pairing 7.5 ms).

## Reading the comments

The code keeps the identifiers of the design it came from, leanKohakuDesktop's
`spec/16-light-client.md` and `spec/INVARIANTS.md` at `8bddee0e`:

- `25a` to `25l`: the light client's invariant rows (25c BLS, 25d the chains, 25e bootstrap,
  25f acceptance, 25g conflicts, 25h the age bound, 25i the clock, 25j EL binding, 25k facts,
  25l inclusion).
- `LC1` to `LC9`: the milestones that built it; `Dn`, `Gn` and "open decision n": the design's
  decisions and goals; `H_vec`, `H_nonce`: named hypotheses.
- `lkd-lc`, `netd`, `keyd`, `lkd_verified`: the wallet's light-client process, network service,
  signer and verified Rust crate, which the comments mention where the wallet uses the code.

## Acknowledgements

leanLight's proofs stand on three projects, whose code is vendored under
`proofs/LeanLightProofs/Vendor/` as the readable specifications the runtime is proved against.
Thank you to their authors:

- **[ssz-specs](https://github.com/ethereum/ssz-specs)** (Ethereum Foundation, MIT), commit
  `3394318c`: SSZ's types, serialization, `hash_tree_root` and Merkle proofs, with their proofs.
  The light client's SSZ decoders, container roots and branch checks are proved against it.
- **[EthLib](https://github.com/ethereum/EthLib)** (CC0-1.0), commit `57af539e`: BLS12-381 in
  Lean, its readable layer and its G1 group-law proofs. KeyValidate, hash-to-G2 and
  FastAggregateVerify are proved equal to EthLib's, and the Jacobian formulas' proofs are
  ported from it.
- **[VCVio](https://github.com/Verified-zkEVM/VCVio)** (Apache-2.0), commit `afa6593f`: SHA-256
  in Lean, the specification the runtime's SHA-256 is proved against.

They are copied, not required: each file names its source commit, and the copies changed only
as their headers say. Thanks also to [Mathlib](https://github.com/leanprover-community/mathlib4),
whose elliptic-curve group law the BLS proofs use, and to
[Helios](https://github.com/a16z/helios), the light client leanLight is measured against.

## License

MIT OR Apache-2.0, at your option (`LICENSE-MIT`, `LICENSE-APACHE`). The vendored code under
`proofs/LeanLightProofs/Vendor/` keeps its own license (`LICENSE` in each directory), and
`scripts/CheckKernel.lean` holds Lean's `leanchecker` replay (Apache-2.0, attributed there).
