"""Test-only: picks the light-client vectors LkdTests.Ssz checks out of an extracted consensus-specs
release (tests/mainnet/...), decompresses each `*.ssz_snappy` (snappy's block format, written out
below; snappy never enters the wallet) and writes the subset under this directory, with
SHA256SUMS. Run as `python3 -I extract.py <release-dir> <this-dir>`; reads only `<release-dir>`.
"""
import hashlib
import re
import sys
from pathlib import Path


def unsnappy(data: bytes) -> bytes:
    """Snappy's raw block format: a varint length, then literals and back-references."""
    pos, length, shift = 0, 0, 0
    while True:
        b = data[pos]; pos += 1
        length |= (b & 0x7F) << shift; shift += 7
        if b < 0x80:
            break
    out = bytearray()
    while pos < len(data):
        tag = data[pos]; pos += 1
        kind = tag & 3
        if kind == 0:  # literal
            n = tag >> 2
            if n >= 60:
                extra = n - 59
                n = int.from_bytes(data[pos:pos + extra], 'little'); pos += extra
            n += 1
            out += data[pos:pos + n]; pos += n
            continue
        if kind == 1:
            n = 4 + ((tag >> 2) & 7)
            off = ((tag >> 5) << 8) | data[pos]; pos += 1
        elif kind == 2:
            n = (tag >> 2) + 1
            off = int.from_bytes(data[pos:pos + 2], 'little'); pos += 2
        else:
            n = (tag >> 2) + 1
            off = int.from_bytes(data[pos:pos + 4], 'little'); pos += 4
        if off == 0 or off > len(out):
            raise ValueError('bad back-reference')
        for _ in range(n):  # copies may overlap
            out.append(out[-off])
    if len(out) != length:
        raise ValueError('length mismatch')
    return bytes(out)


src, dest = Path(sys.argv[1]), Path(sys.argv[2])
base = src / 'tests' / 'mainnet'
picked = []
# ssz_static: the first two random cases of each type LkdLc.Ssz decodes.
types = {'electra': ['BeaconBlockHeader', 'SyncCommittee', 'SyncAggregate', 'ExecutionPayloadHeader',
                     'LightClientHeader', 'LightClientBootstrap', 'LightClientUpdate',
                     'LightClientFinalityUpdate', 'LightClientOptimisticUpdate'],
         'fulu': ['ExecutionPayloadHeader', 'LightClientHeader', 'LightClientBootstrap',
                  'LightClientUpdate', 'LightClientFinalityUpdate', 'LightClientOptimisticUpdate'],
         'gloas': ['BeaconBlockHeader', 'LightClientHeader', 'LightClientBootstrap',
                   'LightClientUpdate', 'LightClientFinalityUpdate', 'LightClientOptimisticUpdate']}
for fork, names in types.items():
    for name in names:
        for case in ('case_0', 'case_1'):
            d = base / fork / 'ssz_static' / name / 'ssz_random' / case
            root = re.search(r"root: '0x([0-9a-f]{64})'", (d / 'roots.yaml').read_text()).group(1)
            out = dest / 'ssz_static' / fork / name / case
            out.mkdir(parents=True, exist_ok=True)
            (out / 'serialized.ssz').write_bytes(unsnappy((d / 'serialized.ssz_snappy').read_bytes()))
            (out / 'root').write_text(root + '\n')
            picked.append(out)
# single_merkle_proof: every light-client proof of Electra, Fulu and Gloas, without the object
# (a BeaconState is about 3 MB): leaf, index, branch, and the object's root.
for fork in ('electra', 'fulu', 'gloas'):
    for proof in sorted((base / fork / 'light_client' / 'single_merkle_proof').glob('*/*')):
        y = (proof / 'proof.yaml').read_text()
        leaf = re.search(r"leaf: '0x([0-9a-f]{64})'", y).group(1)
        index = re.search(r'leaf_index: (\d+)', y).group(1)
        branch = re.findall(r"- '0x([0-9a-f]{64})'", y)
        obj = unsnappy((proof / 'object.ssz_snappy').read_bytes())
        out = dest / 'single_merkle_proof' / fork / proof.parent.name / proof.name
        out.mkdir(parents=True, exist_ok=True)
        (out / 'proof').write_text('\n'.join([leaf, index] + branch) + '\n')
        (out / 'object.sha256').write_text(hashlib.sha256(obj).hexdigest() + '\n')
        if len(obj) < 4096:  # bodies are small: kept, so their root can be recomputed
            (out / 'object.ssz').write_bytes(obj)
        picked.append(out)
sums = []
for f in sorted(p for p in (dest / 'ssz_static').rglob('*') if p.is_file()) + \
        sorted(p for p in (dest / 'single_merkle_proof').rglob('*') if p.is_file()):
    sums.append(f'{hashlib.sha256(f.read_bytes()).hexdigest()}  {f.relative_to(dest)}')
(dest / 'SHA256SUMS').write_text('\n'.join(sums) + '\n')
print(len(picked), 'cases')
