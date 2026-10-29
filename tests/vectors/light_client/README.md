# Light-client vectors for the store

The minimal-preset `light_client/sync` and `light_client/update_ranking` vectors of consensus-specs
**v1.7.0-beta.4** (tag `v1.7.0-beta.4`, commit `aa16bb4c156184e9548a997d53efaf2a228a6304`,
CC0-1.0), for Electra, Fulu and Gloas, decompressed from the release asset `minimal.tar.gz`
(`https://github.com/ethereum/consensus-specs/releases/download/v1.7.0-beta.4/minimal.tar.gz`,
SHA-256 `26d09aea70c62ed235a120a95082d544ab1c2e6fe36bd35ea1bd5da62f3b7b68`, fetched 2026-10-26).
Every case of those directories is here: 1.3 MB. `SHA256SUMS` lists every file.

`lake exe leanlight-store-test` (from `tests`) runs them on `LeanLight.Store`
with the minimal preset's decoders (`LeanLightDev`), under docs/spec-16-light-client.md's rules ("Testing"); nothing here runs in the client.

## What is here

- `<fork>/sync/<case>/`: `bootstrap.ssz` and each update's `.ssz`; `meta.txt` (the genesis
  validators root, the trusted block root, the bootstrap's fork digest and the store's fork
  version); `config.txt` (the fork epochs and versions, `MAX_BLOBS_PER_BLOCK_ELECTRA`,
  `SLOT_DURATION_MS` and `BLOB_SCHEDULE`, from which the test builds the vector's fork table, so
  that its digests are the vector's); `steps.txt`, one step a line with its checks (the finalized
  and optimistic headers' slot, `beacon_root` and `execution_root`). Electra: 5 cases; Fulu: 6
  (`gloas_fork` added); Gloas: 4.
- `<fork>/update_ranking/`: `meta.txt` (the count) and `updates_<i>.ssz`, best first: 57 each.

## The rules the test applies

- Each update is decoded as the fork its digest names, which must be the fork of its attested
  slot, and must be accepted.
- After each step, the finalized header's `slot`, `beacon_root` and `execution_root` are compared,
  and the optimistic header's against the anchor or the finalized header, whichever is newer: leanLight
  has no optimistic header, and every step has full participation. Now is `slotTime(current_slot)`.
- A `force_update` whose checks differ from the previous step's forces an update, which leanLight never
  does (N6): it and the rest of its case are reported **unsupported**, not failed. In
  `light_client_sync` that is steps 6 to 10 of each fork; `*_no_force_update`'s is a no-op.
- `upgrade_store` changes nothing: the store keeps each header in the form it was validated in.
- `update_ranking`: `isBetter` must prefer each update to every later one and never a later one,
  and agree on every pair with the specification's `is_better_update` transcribed as written.

## Regenerating

From an empty directory, stream the asset and extract only these paths:

```sh
curl -fsSL "$url" | tee >(sha256sum) | tar -xzf - --wildcards --no-anchored \
  'tests/minimal/electra/light_client/sync/*' 'tests/minimal/electra/light_client/update_ranking/*' \
  'tests/minimal/fulu/light_client/sync/*' 'tests/minimal/fulu/light_client/update_ranking/*' \
  'tests/minimal/gloas/light_client/sync/*' 'tests/minimal/gloas/light_client/update_ranking/*'
```

check the printed SHA-256 against the one above, then run `python3 -I extract.py <that directory>
.` here. `extract.py` holds the test-only snappy decoder (as `../ssz/extract.py`) and rewrites the
YAML it needs as plain lines; it reads only the directory it is given.
