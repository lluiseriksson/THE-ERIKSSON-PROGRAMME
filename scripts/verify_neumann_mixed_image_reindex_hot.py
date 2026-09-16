#!/usr/bin/env python3
"""Independent exact HOT diagnostic reader; never a production cold seal."""
import argparse
import hashlib
import json
import math
from pathlib import Path
import tarfile
import types

BASE = '46bf719be34e586e83790fa1b2ff2092735faa12'
SOURCE = '49e81d93548ea24d9337c18596caeb8ea7b1b3fb'
DRAFT = 'tmp/NeumannMixedImageReindexDraft.lean'
DIGEST = 'c6e5ebd44a966d71a45c47ec926efb751265cdce27d6e86376d19a7f7ae7f73a'
RUNNER = '6f8acc9e90b545db7a7c211beb15604911e5502fe24ecc0793db2535caf59c66'
GATE = '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'
PREFIX = 'neumann-mixed-image-reindex-hot-v1'
ROOT = '/content/hrpoly-neumann-physical-full-and-mixed-promoted-cold-v1'
NAMES = set([
    "YangMills.RG.neumannMixedBranchFlip_involutive",
    "YangMills.RG.neumannMixedOrbit_full_shift",
    "YangMills.RG.neumannMixedOrbit_proper_reflect",
    "YangMills.RG.neumannMixedImage_periodicIndex",
    "YangMills.RG.neumannMixedImage_properIndex",
    "YangMills.RG.neumannMixedImage_periodic_tsum",
    "YangMills.RG.neumannMixedImage_proper_tsum"
])
COMMANDS = {
    'prerequisites': ['lake', 'build', 'YangMills.RG.NeumannMixedOwnerTransport',
                     'YangMills.RG.NeumannPhysicalPeriodicSeries',
                     'YangMills.RG.NeumannBoundaryImageSeriesReindex'],
    'mixed_reindex': ['lake', 'env', 'lean', DRAFT]}


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
                'prerequisites.log', 'mixed_reindex.log'}
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
    audits = gate.exact_axioms(files['mixed_reindex.log'].decode(), NAMES)
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
    print('MIXED_REINDEX_HOT_EVIDENCE_VERIFIED_NOT_COLD')


if __name__ == '__main__':
    main()

