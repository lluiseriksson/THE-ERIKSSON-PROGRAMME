#!/usr/bin/env python3
"""Read-only verifier for step-13 cold evidence; never invokes Lean or Git."""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import math
from pathlib import Path, PurePosixPath
import re
import tarfile

SOURCE = 'eef777d32878297d9e143cbfaff82c290fbb9be1'
REV = 'cmp99-full-green-arbitrary-residue-cold-v1'
PREFIX = 'hrpoly-cmp99-full-green-arbitrary-residue-cold-v1-evidence'
ROOT = '/content/hrpoly-cmp99-full-green-arbitrary-residue-cold-v1'
MATHLIB = '07642720480157414db592fa85b626dafb71355b'
ASSET = 'bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e'
BASE = '2f097a374361bd8e4c0f53220ffeeeb22fc06d6ccca5179aebda468d1aebee8e'
BLOBS = {
    'YangMills/RG/BalabanCMP99FullGreenArbitraryResidueBound.lean':
        '702ed2e146fd33a5d83ca0843d4c8b58c3efaca3681ad572259fc09a66faccdc',
    'YangMills/RG/BalabanCMP99FullGreenArbitraryResidueBoundAudit.lean':
        '14ca55f49a2c360e527a875bb02e712b5c6a7c2bc588d7e6e42077a76f53a6b2',
}
NAMES = {
    'YangMills.RG.norm_cmp89Eq246PhysicalZeroMassGreen_le_signedLatticeWeight',
    'YangMills.RG.cmp89Eq246DirectedFullSolutionSumBound_nonneg_of_window',
    'YangMills.RG.tsum_norm_cmp89Eq246FullGreen_arbitraryResidue_le_centeredPeriodic',
    'YangMills.RG.norm_tsum_cmp89Eq246FullGreen_arbitraryResidue_le_centeredPeriodic',
}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
REQUIRED = ['download_toolchain', 'extract_toolchain', 'lean_version', 'lake_version',
            'clone', 'checkout', 'head', 'overlay_text_guard', 'import_prefix_guard',
            'lake_update', 'mathlib_pin', 'cache_get',
            'full_green_residue_focal', 'full_green_residue_audit']
LIMIT = 32 * 1024 * 1024


def require(value: bool, message: str) -> None:
    if not value:
        raise RuntimeError(message)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def verify_files(files: dict[str, bytes]) -> dict:
    data = json.loads(files['evidence.json'])
    for key, expected in {'source_sha': SOURCE, 'runner_rev': REV,
                          'mathlib_sha': MATHLIB, 'toolchain_asset_sha256': ASSET,
                          'source_blobs': BLOBS, 'status': 'PASS',
                          'gpu_runtime_authorized': False, 'minimum_ram_gib': 40.0}.items():
        require(data.get(key) == expected, 'EVIDENCE_FIELD=' + key)
    contract = json.loads(files['gate-contract.json'])
    require(contract.get('source_sha') == SOURCE and
            contract.get('base_runner_sha256') == BASE and
            contract.get('project_build_cache_restored') is False and
            contract.get('expected_axiom_names') == sorted(NAMES), 'GATE_CONTRACT')
    preflight = json.loads(files['preflight.json'])
    require(len(preflight) == 2, 'PREFLIGHT_COUNT')
    for record, code in zip(preflight, (0, 7)):
        require(record['actual_exit'] == record['expected_exit'] == code and
                math.isfinite(record['seconds']) and record['seconds'] >= 0,
                'PREFLIGHT_EXIT_TIMER')
    records = data.get('records', [])
    names = [r['stage'] for r in records]
    require(len(names) == len(set(names)), 'DUPLICATE_STAGE')
    require([n for n in names if n in REQUIRED] == REQUIRED, 'REQUIRED_STAGE_ORDER')
    require(set(names) <= set(REQUIRED) | {'apt_update', 'install_zstd'}, 'EXTRA_STAGE')
    indexed = {r['stage']: r for r in records}
    expected_files = {'evidence.json', 'gate-contract.json', 'preflight.json'}
    for record in records:
        stage = record['stage']
        require(record.get('exit') == 0, 'CHILD_EXIT=' + stage)
        elapsed = record.get('seconds')
        require(isinstance(elapsed, (int, float)) and math.isfinite(elapsed)
                and elapsed >= 0, 'CHILD_DURATION=' + stage)
        require(record.get('log_file') == stage + '.log', 'LOG_NAME=' + stage)
        require(sha(files[stage + '.log']) == record.get('output_sha256'),
                'LOG_HASH=' + stage)
        require(json.loads(files[stage + '.json']) == record, 'STAGE_RECORD=' + stage)
        expected_files |= {stage + '.json', stage + '.log'}
    require(set(files) == expected_files, 'ARCHIVE_FILE_SET')
    require(files['head.log'].decode().strip() == SOURCE, 'HEAD_LOG')
    require(files['mathlib_pin.log'].decode().strip() == MATHLIB, 'MATHLIB_LOG')
    for name in ('lean_version', 'lake_version'):
        require('4.29.0-rc6' in files[name + '.log'].decode(), 'VERSION_LOG=' + name)
    require(indexed['checkout']['command'] == ['git', 'checkout', '--detach', SOURCE],
            'CHECKOUT_COMMAND')
    for stage, command in {
        'full_green_residue_focal': ['lake', 'build',
            'YangMills.RG.BalabanCMP99FullGreenArbitraryResidueBound'],
        'full_green_residue_audit': ['lake', 'env', 'lean',
            'YangMills/RG/BalabanCMP99FullGreenArbitraryResidueBoundAudit.lean'],
    }.items():
        require(indexed[stage]['command'] == command and indexed[stage]['cwd'] == ROOT,
                'TARGET_COMMAND=' + stage)
    audit = re.sub(r'\s+', '', files['full_green_residue_audit.log'].decode())
    require(not any(x in audit for x in ('sorryAx', 'ofReduceBool')), 'FORBIDDEN_AXIOM')
    blocks = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", audit)
    require(len(blocks) == len(NAMES) and {name for name, _ in blocks} == NAMES,
            'AXIOM_NAMES')
    for name, body in blocks:
        require(set(filter(None, body.split(','))) <= ALLOWED, 'AXIOM_SET=' + name)
    return {'status': 'PASS', 'source_sha': SOURCE, 'runner_rev': REV,
            'stages_verified': len(records), 'axiom_names_verified': len(blocks),
            'evidence_json_sha256': sha(files['evidence.json']),
            'focal': indexed['full_green_residue_focal'],
            'audit': indexed['full_green_residue_audit']}


def read_archive(path: Path, expected: str) -> dict[str, bytes]:
    require(path.is_file() and path.stat().st_size <= LIMIT, 'ARCHIVE_SIZE')
    require(sha(path.read_bytes()) == expected.lower(), 'ARCHIVE_HASH')
    files = {}
    total = 0
    with tarfile.open(path, 'r:gz') as tf:
        seen = set()
        for member in tf.getmembers():
            require(member.name not in seen, 'DUPLICATE_MEMBER')
            seen.add(member.name)
            parts = PurePosixPath(member.name).parts
            if member.isdir():
                require(parts == (PREFIX,), 'DIRECTORY_MEMBER')
                continue
            require(member.isfile() and len(parts) == 2 and parts[0] == PREFIX
                    and parts[1] not in ('.', '..')
                    and member.name == PREFIX + '/' + parts[1], 'UNSAFE_MEMBER')
            total += member.size
            require(0 <= member.size <= LIMIT and total <= LIMIT, 'EXPANDED_SIZE')
            stream = tf.extractfile(member)
            require(stream is not None, 'UNREADABLE_MEMBER')
            files[parts[1]] = stream.read()
    return files


def self_test() -> None:
    # Synthetic metadata only: these tests are not compilation evidence.
    files = {'gate-contract.json': json.dumps({
        'source_sha': SOURCE, 'base_runner_sha256': BASE,
        'project_build_cache_restored': False,
        'expected_axiom_names': sorted(NAMES)}).encode(),
        'preflight.json': json.dumps([{'actual_exit': n, 'expected_exit': n,
                                      'seconds': .01} for n in (0, 7)]).encode()}
    logs = {'head': SOURCE + '\n', 'mathlib_pin': MATHLIB + '\n',
            'lean_version': 'Lean 4.29.0-rc6', 'lake_version': 'Lake 4.29.0-rc6',
            'full_green_residue_audit': '\n'.join(
                f"'{n}' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]"
                for n in sorted(NAMES))}
    commands = {'checkout': ['git', 'checkout', '--detach', SOURCE],
                'full_green_residue_focal': ['lake', 'build',
                    'YangMills.RG.BalabanCMP99FullGreenArbitraryResidueBound'],
                'full_green_residue_audit': ['lake', 'env', 'lean',
                    'YangMills/RG/BalabanCMP99FullGreenArbitraryResidueBoundAudit.lean']}
    records = []
    for stage in REQUIRED:
        content = logs.get(stage, 'synthetic\n').encode()
        record = {'stage': stage, 'exit': 0, 'seconds': .01,
                  'output_sha256': sha(content), 'log_file': stage + '.log',
                  'command': commands.get(stage, []), 'cwd': ROOT}
        records.append(record)
        files[stage + '.log'] = content
        files[stage + '.json'] = json.dumps(record).encode()
    evidence = {'source_sha': SOURCE, 'runner_rev': REV, 'mathlib_sha': MATHLIB,
                'toolchain_asset_sha256': ASSET, 'source_blobs': BLOBS, 'status': 'PASS',
                'minimum_ram_gib': 40.0, 'gpu_runtime_authorized': False, 'records': records}
    files['evidence.json'] = json.dumps(evidence).encode()
    verify_files(files)
    cases = []
    for key, value in [('source_sha', 'wrong'), ('status', 'FAIL')]:
        bad = dict(files)
        altered = copy.deepcopy(evidence)
        altered[key] = value
        bad['evidence.json'] = json.dumps(altered).encode()
        cases.append(bad)
    bad = dict(files)
    bad['head.log'] += b'corruption'
    cases.append(bad)
    for axiom in ('sorryAx', 'ofReduceBool', 'Unknown.axiom'):
        bad = dict(files)
        altered = copy.deepcopy(evidence)
        content = bad['full_green_residue_audit.log'].replace(b'Quot.sound', axiom.encode())
        altered['records'][-1]['output_sha256'] = sha(content)
        bad['full_green_residue_audit.log'] = content
        bad['full_green_residue_audit.json'] = json.dumps(altered['records'][-1]).encode()
        bad['evidence.json'] = json.dumps(altered).encode()
        cases.append(bad)
    for bad in cases:
        try:
            verify_files(bad)
        except RuntimeError:
            continue
        raise RuntimeError('NEGATIVE_SELF_TEST_ACCEPTED')
    print('VERIFIER_SELF_TEST=PASS positive=1 rejected=' + str(len(cases)))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('archive', nargs='?', type=Path)
    parser.add_argument('--sha256')
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    if args.archive is None or not args.sha256:
        parser.error('archive and --sha256 are required')
    report = verify_files(read_archive(args.archive, args.sha256))
    report['archive_sha256'] = args.sha256.lower()
    print(json.dumps(report, sort_keys=True, indent=2))
    print('FULL_GREEN_RESIDUE_COLD_EVIDENCE_VERIFIED')


if __name__ == '__main__':
    main()
