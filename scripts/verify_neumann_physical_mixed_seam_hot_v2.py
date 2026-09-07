#!/usr/bin/env python3
"""Independent exact HOT diagnostic reader; never a production cold seal."""
import argparse
import hashlib
import json
import math
from pathlib import Path
import tarfile
import types

BASE = 'fa898ff5d8bf724fa4b6e629da7260383ef54ecc'
SOURCE = '0d63d2b0f234d3780b60d6ce1242c6aa8e3f67ae'
DRAFT = 'tmp/NeumannPhysicalMixedSeamDraft.lean'
DIGEST = '8b6a3b21158c3d047e76695c0da179511ae7d353a4be8c95a4da26726e73b155'
RUNNER = '629c64a7b1eff578db16ee8fa20dbac29f9370062775443667fdb89fce6b459b'
GATE = '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'
PREFIX = 'neumann-physical-mixed-seam-hot-v2'
ROOT = '/content/hrpoly-neumann-mixed-image-reindex-promoted-cold-v1'
NAMES = set([
    "YangMills.RG.summable_neumannPhysicalMixedGreenSeries",
    "YangMills.RG.neumannPhysicalMixedGreenSeries_periodic",
    "YangMills.RG.neumannPhysicalMixedGreenSeries_properBoundary"
])
COMMANDS = {'physical_seam': ['lake', 'env', 'lean', DRAFT]}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require(test, label):
    if not test:
        raise ValueError(label)


def read_archive(path, digest):
    require(path.stat().st_size <= 4 * 1024**2, 'ARCHIVE_SIZE')
    require(sha(path.read_bytes()) == digest.lower(), 'ARCHIVE_HASH')
    files = {}
    total = 0
    with tarfile.open(path) as tar:
        for m in tar:
            if m.isdir():
                require(m.name.rstrip('/') == PREFIX, 'EXTRA_DIRECTORY')
                continue
            require(m.isfile() and m.name.startswith(PREFIX + '/'), 'MEMBER_TYPE')
            name = m.name[len(PREFIX) + 1:]
            require('/' not in name and name not in files and name not in ('', '.', '..'), 'MEMBER_NAME')
            total += m.size
            require(total <= 32 * 1024**2 and len(files) < 12, 'MEMBER_LIMIT')
            files[name] = tar.extractfile(m).read()
    return files


def verify(files, gate):
    expected = {'runner.py', 'source.lean', 'result.json', 'manifest.json',
                'physical_seam.log'}
    require(set(files) == expected, 'FILE_SET')
    manifest = json.loads(files['manifest.json'])
    require(set(manifest) == expected - {'manifest.json'}, 'MANIFEST_SET')
    for name, digest in manifest.items():
        require(sha(files[name]) == digest, 'MEMBER_HASH=' + name)
    require(sha(files['runner.py']) == RUNNER, 'RUNNER_HASH')
    require(sha(files['source.lean']) == DIGEST, 'SOURCE_HASH')
    r = json.loads(files['result.json'])
    for key, value in dict(status='PASS', cold_seal=False, base_source=BASE,
            overlay_source=SOURCE, overlay_path=DRAFT, overlay_sha256=DIGEST,
            expected_names=sorted(NAMES)).items():
        require(r.get(key) == value, 'RESULT=' + key)
    require([s['stage'] for s in r['records']] == list(COMMANDS), 'STAGE_ORDER')
    for s in r['records']:
        require(s['command'] == COMMANDS[s['stage']] and s['cwd'] == ROOT, 'COMMAND')
        require(s['exit'] == 0 and isinstance(s['seconds'], (int, float)) and
                math.isfinite(s['seconds']) and s['seconds'] >= 0, 'EXIT_OR_TIME')
        require(s['log_sha256'] == sha(files[s['stage'] + '.log']), 'LOG_HASH')
    audits = gate.exact_axioms(files['physical_seam.log'].decode(), NAMES)
    require(r['audits'] == audits, 'AUDIT_RECORD')
    return dict(status='PASS', cold_seal=False, source=SOURCE, source_sha256=DIGEST,
                records=r['records'], audits=audits)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--archive', type=Path, required=True)
    p.add_argument('--sha256', required=True)
    p.add_argument('--helpers', type=Path, required=True)
    args = p.parse_args()
    data = (args.helpers / 'full_green_owner_exact_axiom_gate.py').read_bytes()
    require(sha(data) == GATE, 'GATE_HASH')
    gate = types.ModuleType('exact_gate')
    exec(compile(data, 'exact_gate', 'exec'), gate.__dict__)
    print(json.dumps(verify(read_archive(args.archive, args.sha256), gate), sort_keys=True))
    print('PHYSICAL_MIXED_SEAM_HOT_EVIDENCE_VERIFIED_NOT_COLD')


if __name__ == '__main__':
    main()

