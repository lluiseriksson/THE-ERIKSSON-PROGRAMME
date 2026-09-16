"""Verify all cold evidence before preservation; bounded I/O, no compiler/network/pool."""
import argparse
import json
import math
from pathlib import Path
import types

from verify_neumann_counting_reflection_diagnostic_v2 import unpack, require, sha

SOURCE = '87edca6519df5b450b906e83db2ffa4fc1bd87bd'
REV = 'neumann-integer-image-promoted-cold-v1'
LAUNCHER = 'launch_neumann_integer_image_promoted_cold.py'
LAUNCHER_HASH = '0026a86bb1db3a7dea2d0166375c9b0b58eda4bb9160bd58378020fe4e54d162'
PINS = {
    'colab_neumann_integer_image_promoted_cold.py': ('8564dbfee39468e7a6d50e52e4173c0da844d315', '9f2ea3bcb492125c7e20d8ceb761128421baedb7695e9b56b97d2ffe4b9317ec'),
    'verify_neumann_integer_image_promoted_cold.py': ('8564dbfee39468e7a6d50e52e4173c0da844d315', 'b505adb82b52eb7bb3abf3dc8874bb291aee5e2b9c5d9c687b392878430ac957'),
    'verify_cmp99_full_green_residue_cold.py': (SOURCE, '558295bb43e74bdae3eb6508656e7b8cde756cb393376320d0c197347396a02c'),
    'full_green_owner_exact_axiom_gate.py': (SOURCE, '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'),
}

def load(blob, name):
    require(sha(blob) == PINS[name][1], 'HELPER_HASH=' + name)
    module = types.ModuleType(name)
    exec(compile(blob, name, 'exec'), module.__dict__)
    return module

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--archive', type=Path, required=True)
    p.add_argument('--outer-sha256', required=True)
    p.add_argument('--destination', type=Path)
    a = p.parse_args()
    require(a.archive.stat().st_size <= 64 * 2**20, 'ARCHIVE_SIZE')
    blob = a.archive.read_bytes()
    require(sha(blob) == a.outer_sha256.lower(), 'OUTER_HASH')
    if a.destination:
        require(not a.destination.exists(), 'NO_OVERWRITE')
    outer = unpack(blob)
    prefix = REV + '-launch/'
    inner_name = 'hrpoly-' + REV + '-evidence.tar.gz'
    stages = ['verifier_self_test', 'physical_cold_graph', 'archive_verifier']
    expected = {LAUNCHER, inner_name, *(prefix + n for n in PINS),
        prefix + 'transport.json', prefix + 'launch-records.json', prefix + 'launch-final-status.json',
        *(prefix + s + '.log' for s in stages)}
    require(set(outer) == expected, 'OUTER_FILES')
    require(sha(outer[LAUNCHER]) == LAUNCHER_HASH, 'LAUNCHER_HASH')
    require(json.loads(outer[prefix + 'transport.json']) == {n: list(v) for n, v in PINS.items()}, 'TRANSPORT')
    for name, (_, digest) in PINS.items():
        require(sha(outer[prefix + name]) == digest, 'PAYLOAD=' + name)
    require(json.loads(outer[prefix + 'launch-final-status.json']) ==
        dict(status='PASS', source=SOURCE, revision=REV, cold_seal=True), 'FINAL_STATUS')
    records = json.loads(outer[prefix + 'launch-records.json'])
    require([r['stage'] for r in records] == stages, 'LAUNCH_ORDER')
    work = '/content/' + REV + '-launch/'
    py = records[0]['command'][0]
    require(py in ('/usr/bin/python3', '/usr/local/bin/python3'), 'PYTHON')
    verifier = work + 'verify_neumann_integer_image_promoted_cold.py'
    commands = [[py, verifier, '--helpers', work.rstrip('/'), '--self-test'],
        [py, work + 'colab_neumann_integer_image_promoted_cold.py'],
        [py, verifier, '--helpers', work.rstrip('/'), '--archive', '/content/' + inner_name,
            '--sha256', sha(outer[inner_name])]]
    for r, cmd in zip(records, commands):
        require(r['exit'] == 0 and r['command'] == cmd, 'LAUNCH_CHILD=' + r['stage'])
        require(math.isfinite(r['seconds']) and r['seconds'] >= 0, 'LAUNCH_TIMER')
        require(sha(outer[prefix + r['stage'] + '.log']) == r['log_sha256'], 'LAUNCH_LOG')
    cold = load(outer[prefix + 'verify_neumann_integer_image_promoted_cold.py'], 'verify_neumann_integer_image_promoted_cold.py')
    old = load(outer[prefix + 'verify_cmp99_full_green_residue_cold.py'], 'verify_cmp99_full_green_residue_cold.py')
    gate = load(outer[prefix + 'full_green_owner_exact_axiom_gate.py'], 'full_green_owner_exact_axiom_gate.py')
    nested = unpack(outer[inner_name])
    inner_prefix = 'hrpoly-' + REV + '-evidence/'
    require(all(n.startswith(inner_prefix) for n in nested), 'INNER_PREFIX')
    files = {n[len(inner_prefix):]: b for n, b in nested.items()}
    report = cold.verify(files, gate, old)
    result = dict(status='PASS', source=SOURCE, outer_sha256=sha(blob),
        inner_sha256=sha(outer[inner_name]), launch=records, cold=report,
        scope='intermediate integer image-owner-indicator; not physical Q intertwining, regional inverse or window15')
    payload = (json.dumps(result, sort_keys=True, indent=2) + '\n').encode()
    if a.destination:
        require(not set(outer).intersection(nested), 'PATH_COLLISION')
        root = a.destination
        root.mkdir(parents=True, exist_ok=False)
        (root / a.archive.name).write_bytes(blob)
        for name, content in {**outer, **nested}.items():
            target = root / Path(name)
            target.parent.mkdir(parents=True, exist_ok=True)
            with target.open('xb') as out:
                out.write(content)
        (root / 'independent-local-verification.json').write_bytes(payload)
    print('NEUMANN_INTEGER_IMAGE_PROMOTED_COLD_PRESERVATION=PASS')
    print('REPORT_SHA256=' + sha(payload))
    print(payload.decode(), end='')

if __name__ == '__main__':
    main()

