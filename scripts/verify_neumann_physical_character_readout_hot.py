#!/usr/bin/env python3
"""Independent HOT-only reader for literal physical character/readout diagnostics."""
import hashlib
import json
import math
from pathlib import Path
import tarfile

SOURCE = '98f4337e06271a7d5e3957450440292db0f79168'
ROOT = '/content/hrpoly-neumann-character-normalization-promoted-cold-v1'
PREFIX = 'neumann-physical-character-readout-hot-v1'
OVERLAY_SOURCE = 'ce9cc5cc858214ee4e80fca27e6854d22567f653'
RUNNER = '613f9dfa4751cf79546c4923efc8a94717d2128a351999619f009606051732ac'
DRAFTS = {
    "tmp/NeumannPhysicalBrillouinCharacterDraft.lean": "c845da5c7961927047d0e8974031d2ff29c7791d7be8bb6113c99f16dc44dc75",
    "tmp/NeumannAliasPrecisionReadoutDraft.lean": "ddcc7a677396a175bea22e002304b00fe4c9b89de52f2714605eb59b3f5e2274"
}
NAMES = {
    "physical_character_repro": [
        "YangMills.RG.neumannTorus_volumeCharacterIntegral",
        "YangMills.RG.neumannPhysicalBrillouin_character_phase",
        "YangMills.RG.neumannPhysicalBrillouin_integerCharacterIntegral"
    ],
    "alias_readout_repro": [
        "YangMills.RG.neumannAliasPrecision_finePointSource_readout"
    ]
}
COMMANDS = {
    "physical_character_prerequisites": [
        "lake",
        "build",
        "YangMills.RG.BalabanCMP89NormalizedBrillouinToTorusMeasure",
        "YangMills.RG.BalabanCMP89Eq246FullSolutionDomain"
    ],
    "physical_character_repro": [
        "lake",
        "env",
        "lean",
        "tmp/NeumannPhysicalBrillouinCharacterDraft.lean"
    ],
    "alias_readout_repro": [
        "lake",
        "env",
        "lean",
        "tmp/NeumannAliasPrecisionReadoutDraft.lean"
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
