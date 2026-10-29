"""Test-only: picks the minimal-preset light-client vectors LkdTests.Store checks out of an
extracted consensus-specs release (tests/minimal/...): `light_client/sync` and
`light_client/update_ranking` of Electra, Fulu and Gloas. Decompresses each `*.ssz_snappy`
(snappy's block format, as ../ssz/extract.py; snappy never enters the wallet) and rewrites the
YAML it needs as plain lines (no YAML parser runs in Lean):

  config.txt   `KEY value` for the fork epochs and versions, MAX_BLOBS_PER_BLOCK_ELECTRA,
               SLOT_DURATION_MS, and `BLOB epoch max` per BLOB_SCHEDULE entry
  meta.txt     gvr, trusted block root, bootstrap fork digest, store fork version (sync)
               or the update count (update_ranking, which has no config: ranking reads the
               preset only)
  steps.txt    one step a line, then its checks (finalized slot, beacon root, execution root,
               then the optimistic header's):
                 process_update <digest> <file> <current_slot> <checks>
                 force_update <current_slot> <checks>
                 upgrade_store <store_fork_version> <checks>

Run as `python3 -I extract.py <release-dir> <this-dir>`; reads only `<release-dir>`, and writes
SHA256SUMS over everything it wrote.
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


KEYS = ['ELECTRA_FORK_EPOCH', 'ELECTRA_FORK_VERSION', 'FULU_FORK_EPOCH', 'FULU_FORK_VERSION',
        'GLOAS_FORK_EPOCH', 'GLOAS_FORK_VERSION', 'MAX_BLOBS_PER_BLOCK_ELECTRA', 'SLOT_DURATION_MS']


def config(text: str) -> str:
    lines = []
    for k in KEYS:
        m = re.search(r'^' + k + r": '?([0-9a-fx]+)'?$", text, re.M)
        if m:
            lines.append(f'{k} {m.group(1)}')
    sched = re.search(r'^BLOB_SCHEDULE:\n((?:  .*\n)*)', text, re.M)
    if sched:
        body = sched.group(1)
        for e, m in re.findall(r'- EPOCH: (\d+)\n\s+MAX_BLOBS_PER_BLOCK: (\d+)', body):
            lines.append(f'BLOB {e} {m}')
    return '\n'.join(lines) + '\n'


def checks(block: str) -> str:
    vals = []
    for h in ('finalized_header', 'optimistic_header'):
        m = re.search(h + r":\s*\n\s+slot: (\d+)\s*\n\s+beacon_root: '0x([0-9a-f]{64})'\s*\n"
                      r"\s+execution_root: '0x([0-9a-f]{64})'", block)
        vals += [m.group(1), m.group(2), m.group(3)]
    return ' '.join(vals)


def steps(text: str) -> str:
    out = []
    for block in re.split(r'^- ', text, flags=re.M)[1:]:
        kind = block.split(':', 1)[0]
        if kind == 'process_update':
            d = re.search(r"update_fork_digest: '0x([0-9a-f]{8})'", block).group(1)
            f = re.search(r'^\s+update:\s*\n?\s*(update_\S+)', block, re.M).group(1)
            s = re.search(r'current_slot: (\d+)', block).group(1)
            out.append(f'process_update {d} {f} {s} {checks(block)}')
        elif kind == 'force_update':
            s = re.search(r'current_slot: (\d+)', block).group(1)
            out.append(f'force_update {s} {checks(block)}')
        elif kind == 'upgrade_store':
            v = re.search(r"store_fork_version: '0x([0-9a-f]{8})'", block).group(1)
            out.append(f'upgrade_store {v} {checks(block)}')
        else:
            raise ValueError('unknown step ' + kind)
    return '\n'.join(out) + '\n'


src, dest = Path(sys.argv[1]), Path(sys.argv[2])
base = src / 'tests' / 'minimal'
written = []


def write(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
    written.append(path)


for fork in ('electra', 'fulu', 'gloas'):
    for case in sorted((base / fork / 'light_client' / 'sync' / 'pyspec_tests').iterdir()):
        out = dest / fork / 'sync' / case.name
        write(out / 'config.txt', config((case / 'config.yaml').read_text()).encode())
        meta = (case / 'meta.yaml').read_text()
        vals = [re.search(k + r": '0x([0-9a-f]+)'", meta).group(1) for k in
                ('genesis_validators_root', 'trusted_block_root', 'bootstrap_fork_digest',
                 'store_fork_version')]
        write(out / 'meta.txt', (' '.join(vals) + '\n').encode())
        write(out / 'steps.txt', steps((case / 'steps.yaml').read_text()).encode())
        for f in sorted(case.glob('*.ssz_snappy')):
            write(out / (f.name[:-len('.ssz_snappy')] + '.ssz'), unsnappy(f.read_bytes()))
    case = base / fork / 'light_client' / 'update_ranking' / 'pyspec_tests' / 'update_ranking'
    out = dest / fork / 'update_ranking'
    count = int(re.search(r'updates_count: (\d+)', (case / 'meta.yaml').read_text()).group(1))
    write(out / 'meta.txt', f'{count}\n'.encode())
    for i in range(count):
        write(out / f'updates_{i}.ssz', unsnappy((case / f'updates_{i}.ssz_snappy').read_bytes()))

sums = sorted(f'{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.relative_to(dest)}' for p in written)
(dest / 'SHA256SUMS').write_text('\n'.join(sums) + '\n')
print(len(written), 'files')
