#!/usr/bin/env python3
"""Independent HOT-only reader for finite character normalization diagnostics."""
import hashlib
import json
import math
from pathlib import Path
import tarfile

SOURCE = 'a5811d5ddd78faf6fe638aa00db30276af826baf'
ROOT = '/content/hrpoly-neumann-physical-mixed-seam-promoted-cold-v1'
PREFIX = 'neumann-pointsource-normalization-hot-v1'
RUNNER = '72b5a1542213276b49a1f68861724769f62b5af8367a84ce7270b83da8cb25ec'
DRAFTS = {
    "tmp/NeumannTorusCharacterIntegralRepro.lean": "78e060fc4b296ca2aa14b79281850e6f0921fd17df183f24b809d18754c64317",
    "tmp/NeumannCenteredAliasCharacterDraft.lean": "33e22d4852cbdf17f2d44445528fef1afbd2106f9b63c74d6ca10c867a926b53"
}
NAMES = {
    "haar_repro": [
        "YangMills.RG.neumannUnitCircle_volume_eq_normalizedHaar",
        "YangMills.RG.neumannTorus_normalizedCharacterIntegral"
    ],
    "alias_repro": [
        "YangMills.RG.neumannCenteredAliasVectorResidueEquiv_apply",
        "YangMills.RG.neumannCenteredAlias_character_sum",
        "YangMills.RG.neumannIntegerCharacter_product_phase"
    ]
}
COMMANDS = {
    "haar_repro": [
        "lake",
        "env",
        "lean",
        "tmp/NeumannTorusCharacterIntegralRepro.lean"
    ],
    "alias_prerequisites": [
        "lake",
        "build",
        "YangMills.RG.BalabanCMP99SourceCenteredAliasReflection",
        "YangMills.RG.BalabanCMP99FlatMultidimensionalDFT"
    ],
    "alias_repro": [
        "lake",
        "env",
        "lean",
        "tmp/NeumannCenteredAliasCharacterDraft.lean"
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
                     source_blobs=DRAFTS, expected_names=NAMES).items():
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

