#!/usr/bin/env python3
"""Independent HOT-only reader for literal alias exponential selector diagnostics."""
import hashlib
import json
import math
from pathlib import Path
import tarfile

SOURCE = '29a48ac4bb1058cd71b74f65029e918d49e74b60'
ROOT = '/content/hrpoly-neumann-physical-character-promoted-cold-v1'
PREFIX = 'neumann-alias-exponential-selector-hot-v1'
OVERLAY_SOURCE = '0dcd87f8b60dfb464fb3a6707b8f65fe96637960'
RUNNER = 'f6d838590726f31b1123b356ff7b0991df5a8c206a0e3e6464ef267106590b09'
DRAFTS = {
    "tmp/NeumannAliasExponentialSelectorDraft.lean": "48777e553acc6f908a78bc3de7f04ad42068fd1d53a56a60f41449e2f15d2e01"
}
NAMES = {
    "selector_repro": [
        "YangMills.RG.neumannIntegerVectorCharacter_phase",
        "YangMills.RG.neumannCenteredAlias_exponential_sum",
        "YangMills.RG.neumannCenteredAlias_shiftedPhase_sum"
    ]
}
COMMANDS = {
    "selector_prerequisites": [
        "lake",
        "build",
        "YangMills.RG.NeumannCenteredAliasCharacter"
    ],
    "selector_repro": [
        "lake",
        "env",
        "lean",
        "tmp/NeumannAliasExponentialSelectorDraft.lean"
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
