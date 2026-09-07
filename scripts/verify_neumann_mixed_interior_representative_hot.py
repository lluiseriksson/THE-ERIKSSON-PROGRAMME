#!/usr/bin/env python3
"""Independent HOT-only reader for literal alias physical-integral diagnostics."""
import hashlib
import json
import math
from pathlib import Path
import tarfile

SOURCE = '3391796fbcd65fa8f4453f5e482b36bc19f455c6'
ROOT = '/content/hrpoly-neumann-physical-readout-integral-promoted-cold-v1'
PREFIX = 'neumann-mixed-interior-representative-hot-v1'
OVERLAY_SOURCE = '70ddeb82b2825e6fff7a206138ed71b8b4f151c5'
RUNNER = 'a38d61d947842aef7c79b232f381c81fa4198c4b6fbde8e620f8b434148038d2'
DRAFTS = {
    "tmp/NeumannMixedInteriorRepresentativeDraft.lean": "79d8575136ac932937ca4e7b224d59a7446f8423aa4c4baf9463fc0429af9538"
}
NAMES = {
    "interior_representative": [
        "YangMills.RG.neumannMixedInteriorRepresentative_image",
        "YangMills.RG.neumannMixedCoordinateImage_eq_interior_iff",
        "YangMills.RG.neumannMixedFamilyImage_eq_interior_iff"
    ]
}
COMMANDS = {
    "coverage_prerequisite": [
        "lake",
        "build",
        "YangMills.RG.NeumannMixedCoordinateCoverage"
    ],
    "interior_representative": [
        "lake",
        "env",
        "lean",
        "tmp/NeumannMixedInteriorRepresentativeDraft.lean"
    ]
}
GATE = '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def require(value, label):
    if not value:
        raise ValueError(label)

def read_archive(path, digest):
    require(path.stat().st_size <= 4 * 1024**2, 'ARCHIVE_SIZE')
    require(sha(path.read_bytes()) == digest.lower(), 'ARCHIVE_HASH')
    files, total = {}, 0
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
    expected = {'runner.py', 'result.json', 'manifest.json'}
    expected |= {Path(p).name for p in DRAFTS}
    expected |= {s + '.log' for s in COMMANDS}
    require(set(files) == expected, 'FILE_SET')
    manifest = json.loads(files['manifest.json'])
    require(set(manifest) == expected - {'manifest.json'}, 'MANIFEST_SET')
    for name, digest in manifest.items():
        require(sha(files[name]) == digest, 'MEMBER_HASH=' + name)
    require(sha(files['runner.py']) == RUNNER, 'RUNNER_HASH')
    for p, digest in DRAFTS.items():
        require(sha(files[Path(p).name]) == digest, 'SOURCE_HASH=' + p)
    result = json.loads(files['result.json'])
    for k, v in dict(status='PASS', cold_seal=False, source_sha=SOURCE,
                     source_blobs=DRAFTS, overlay_source_sha=OVERLAY_SOURCE, expected_names=NAMES).items():
        require(result.get(k) == v, 'RESULT=' + k)
    require([s['stage'] for s in result['records']] == list(COMMANDS), 'STAGE_ORDER')
    for r in result['records']:
        require(r['command'] == COMMANDS[r['stage']] and r['cwd'] == ROOT, 'COMMAND')
        require(r['exit'] == 0 and isinstance(r['seconds'], (int, float)) and
                math.isfinite(r['seconds']) and r['seconds'] >= 0, 'EXIT_OR_TIME')
        require(r['log_sha256'] == sha(files[r['stage'] + '.log']), 'LOG_HASH')
    audits = {s: gate.exact_axioms(files[s + '.log'].decode(), set(ns))
              for s, ns in NAMES.items()}
    require(result['audits'] == audits, 'AUDIT_RECORD')
    return dict(status='PASS', cold_seal=False, source_sha=SOURCE,
                records=result['records'], audits=audits)

