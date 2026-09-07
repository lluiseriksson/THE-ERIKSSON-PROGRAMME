#!/usr/bin/env python3
"""Independent HOT-only reader for literal alias physical-integral diagnostics."""
import hashlib
import json
import math
from pathlib import Path
import tarfile

SOURCE = '1885a6c0886e595f0d3013c6ac2b9a71f3c93036'
ROOT = '/content/hrpoly-neumann-selector-opposite-promoted-cold-v1'
PREFIX = 'neumann-alias-physical-integral-hot-v3'
OVERLAY_SOURCE = 'cd95bb263e73bbac9bcaeae540925a4df343d866'
RUNNER = '75d0c7182d2730087f4a0d4a7cfc88a4bd97f95fc6e319c3c3b53281020a48c7'
DRAFTS = {
    "tmp/NeumannIntegralRewriteRepro.lean": "2f1fe353cce9fcb15a90f347b006b718e5857c73918a866eeb2402525000dd92",
    "tmp/NeumannAliasPhysicalIntegralDraft.lean": "ac631ace0f5b6348dc0b944c2faf6aa17702748334ac043098baebaa7f3bd8c7"
}
NAMES = {
    "rewrite_repro": [
        "YangMills.RG.neumannReproNormalizedIntegral_mul",
        "YangMills.RG.neumannReproDependentZeroIf",
        "YangMills.RG.neumannReproZeroCast"
    ],
    "physical_integral": [
        "YangMills.RG.neumannZeroResidue_exists_integerQuotient",
        "YangMills.RG.neumannIntegerQuotient_phase",
        "YangMills.RG.neumannIntegerQuotient_zero_iff",
        "YangMills.RG.neumannCenteredAlias_physicalIntegral"
    ]
}
COMMANDS = {
    "rewrite_repro": [
        "lake",
        "env",
        "lean",
        "tmp/NeumannIntegralRewriteRepro.lean"
    ],
    "physical_integral": [
        "lake",
        "env",
        "lean",
        "tmp/NeumannAliasPhysicalIntegralDraft.lean"
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
