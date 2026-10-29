# SSZ vectors for the light client

A subset of the consensus-specs **v1.7.0-beta.4** test vectors (tag `v1.7.0-beta.4`, commit
`aa16bb4c156184e9548a997d53efaf2a228a6304`, CC0-1.0), mainnet preset, decompressed from the
release asset `mainnet.tar.gz`
(`https://github.com/ethereum/consensus-specs/releases/download/v1.7.0-beta.4/mainnet.tar.gz`,
SHA-256 `67762986572372a08d3b182535aa760433c86e174e14e0bbd756f350dd19398c`, fetched
2026-10-26). `SHA256SUMS` lists every file here.

`lake exe lkd-ssz-test` (from `proofs/tests`) checks them against `LkdLc.Ssz`
(`LkdTests/Ssz.lean`); nothing here runs in the wallet.

## What is here

- `ssz_static/<fork>/<type>/case_{0,1}`: `serialized.ssz` and its `root` (from `roots.yaml`), the
  first two `ssz_random` cases of each type `LkdLc.Ssz` decodes: `BeaconBlockHeader`,
  `SyncCommittee`, `SyncAggregate`, `ExecutionPayloadHeader` and `LightClient{Header,Bootstrap,
  Update,FinalityUpdate,OptimisticUpdate}` of Electra; `ExecutionPayloadHeader` and the five
  `LightClient*` of Fulu; `BeaconBlockHeader` and the five `LightClient*` of Gloas. 42 cases.
  Each is decoded, encoded again by the test's encoders (back to the same bytes), and hashed (to
  the same root); then mutated (a byte more or less for a fixed-size container, each offset moved
  by 1, -1 or 4, 33 more bytes of `extra_data`), and every mutation must be refused.
- `single_merkle_proof/<fork>/<object>/<proof>`: `proof` (leaf, gindex, then the branch, one hex
  value a line, from `proof.yaml`) for every light-client proof of Electra, Fulu and Gloas: the
  `BeaconState`'s committees and finalized root, the `BeaconBlockBody`'s execution payload
  (Electra, Fulu) and execution block hash (Gloas). 12 cases. Each gindex must be the one
  `LkdLc.Ssz` pins, each branch as long as its depth; the branch must verify under the root it
  climbs to, with a leading zero root added too, and fail with a leading non-zero root, a short
  branch, another leaf, a deeper gindex, the sibling's gindex (unless leaf and sibling are equal)
  or any node altered. `object.sha256` is the SHA-256 of the decompressed object; the
  `BeaconBlockBody` objects (under 1 KB) are kept as `object.ssz`, the `BeaconState`s (about
  3 MB each) are not.

**Not checked**: that the root a branch climbs to is the object's `hash_tree_root`. That needs
`hash_tree_root` of a whole `BeaconState` or `BeaconBlockBody`, which the light client never
computes and `LkdLc.Ssz` does not implement. The gindices themselves are proved
(`LkdProofs.Lc.SszGindex`); the vectors check them against the specification's own proofs.

## Regenerating

From an empty directory, stream the asset and extract only these paths:

```sh
curl -fsSL "$url" | tee >(sha256sum) | tar -xzf - --wildcards --no-anchored \
  'tests/mainnet/*/ssz_static/LightClient*' 'tests/mainnet/*/ssz_static/BeaconBlockHeader/*' \
  'tests/mainnet/*/ssz_static/SyncCommittee/*' 'tests/mainnet/*/ssz_static/SyncAggregate/*' \
  'tests/mainnet/*/ssz_static/ExecutionPayloadHeader/*' \
  'tests/mainnet/*/light_client/single_merkle_proof/*'
```

check the printed SHA-256 against the one above, then run
`python3 -I extract.py <that directory> .` here. `extract.py` holds the test-only snappy decoder
(the raw block format of `*.ssz_snappy`); it reads only the directory it is given.
