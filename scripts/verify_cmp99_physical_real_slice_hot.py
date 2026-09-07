"""Read-only verifier of the bounded F5 physical real-slice HOT archive.

No subprocess, network, Lean, extraction or source mutation. PASS here
verifies a diagnostic package, never a cold seal or regional B0.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import math
from pathlib import Path
import tarfile
import types

SOURCE = 'e833ec7e7e52ce4dbb1431777e715039ae567c23'
COLD_SOURCE = '6c49a8daeb6d6c6f60ac4a2cd2bafda67a495ff4'
REV = 'cmp99-physical-green-real-slice-hot-v1'
ROOT = '/content/hrpoly-cmp99-point-fibre-promoted-cold-v1'
LOGS = '/content/' + REV + '-logs'
HELPERS = '/content/f5-promoted-cold-launch'
PYTHON = '/usr/bin/python3'
BLOBS = {
    'tmp/SourceFlowPhysicalCarrierRepro.lean':
        '514b495a62334452fecafff32bc98f834da1746df83e5694b051078a0b8d4fd2',
    'tmp/SourceFlowPhysicalGreenRealSliceDraft.lean':
        'fea0b88dfc785bf5b896233654484a05e0ffbb6daf3ef81d82cb8e2c648cc00b',
}
HELPER_HASHES = {
    'verify_cmp99_point_fibre_promoted_cold.py':
        'f9a1c8b85731e8203d9046860005a1a0f867298ca2b33be3abf17396612f0a51',
    'verify_cmp99_full_green_residue_cold.py':
        '558295bb43e74bdae3eb6508656e7b8cde756cb393376320d0c197347396a02c',
    'full_green_owner_exact_axiom_gate.py':
        '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
}
EXPECTED = frozenset('YangMills.RG.' + name for name in (
    'cmp99SourceFlowPhysicalAmbientGreen_ofReal_draft',
    'cmp99SourceFlowPhysicalStep7bFieldEquiv_apply_site_draft',
    'cmp99SourceFlowPhysicalStep7bGreen_ofReal_draft',
    'norm_cmp99SourceFlowPhysicalStep7bGreen_ofReal_apply_draft',
))


def sha(blob):
    return hashlib.sha256(blob).hexdigest()


def require(ok, message):
    if not ok:
        raise ValueError(message)


def read_archive(path, digest):
    require(path.stat().st_size <= 16000000, 'ARCHIVE_SIZE')
    require(sha(path.read_bytes()) == digest.lower(), 'ARCHIVE_HASH')
    prefix = REV + '-logs/'
    files, total = {}, 0
    with tarfile.open(path, 'r:gz') as archive:
        for member in archive:
            if member.isdir():
                require(member.name.rstrip('/') == prefix.rstrip('/'), 'DIRECTORY_NAME')
                continue
            require(member.isfile() and 0 <= member.size <= 8000000, 'MEMBER_KIND_OR_SIZE')
            require(member.name.startswith(prefix), 'MEMBER_PREFIX')
            name = member.name[len(prefix):]
            require(name and '/' not in name and '\\' not in name and name not in ('.', '..'),
                    'MEMBER_PATH')
            require(name not in files, 'DUPLICATE_MEMBER')
            total += member.size
            require(total <= 32000000, 'TOTAL_MEMBER_SIZE')
            files[name] = archive.extractfile(member).read()
    return files


def commands(cold_hash):
    return {
        'verify_cold_evidence': [PYTHON, HELPERS + '/verify_cmp99_point_fibre_promoted_cold.py',
            '--helpers', HELPERS, '--archive', ROOT + '-evidence.tar.gz', '--sha256', cold_hash],
        'retained_head': ['git', 'rev-parse', 'HEAD'],
        'retained_clean': ['git', 'diff', '--exit-code', 'HEAD', '--',
            'YangMills', 'lean-toolchain', 'lake-manifest.json'],
        'mathlib_pin': ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'],
        'text_guard': [PYTHON, 'scripts/check_lean_overlay_text.py',
            '--paths-from', LOGS + '/paths.txt', '--require-prevalidation'],
        'import_guard': [PYTHON, 'scripts/check_lean_import_prefix.py', *BLOBS],
        'mathlib_carrier_repro': ['lake', 'env', 'lean', '-o',
            LOGS + '/SourceFlowPhysicalCarrierRepro.olean', 'tmp/SourceFlowPhysicalCarrierRepro.lean'],
        'physical_prerequisites': ['lake', 'build',
            'YangMills.RG.FinitePiLpRealSliceFibreTransport',
            'YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalGreenIdentification'],
        'physical_real_slice_draft': ['lake', 'env', 'lean', '-o',
            LOGS + '/SourceFlowPhysicalGreenRealSliceDraft.olean',
            'tmp/SourceFlowPhysicalGreenRealSliceDraft.lean'],
        'final_clean': ['git', 'diff', '--exit-code', 'HEAD', '--',
            'YangMills', 'lean-toolchain', 'lake-manifest.json'],
    }


def verify(files, cold_hash, gate):
    data = json.loads(files['debug-evidence.json'])
    require(data['runner_rev'] == REV and data['draft_source'] == SOURCE and
            data['retained_source'] == COLD_SOURCE, 'SOURCE_OR_REVISION')
    require(data['cold_seal'] is False, 'HOT_IS_NOT_COLD')
    require(data['cold_archive_sha256'] == cold_hash, 'PARENT_COLD_HASH')
    require(data['source_blobs'] == BLOBS and data['helper_hashes'] == HELPER_HASHES, 'PIN_MAPS')
    require(data['status'] in ('PASS', 'FAIL'), 'STATUS')
    require(set(files) == set(data['files']) | {'debug-evidence.json'}, 'EXACT_FILE_SET')
    for name, digest in data['files'].items():
        require(sha(files[name]) == digest, 'FILE_HASH=' + name)
    queue = commands(cold_hash)
    records = data['records']
    require([r['stage'] for r in records] == list(queue)[:len(records)], 'STAGE_PREFIX')
    allowed = {'debug-evidence.json', 'records.json', 'paths.txt'} | {
        Path(path).name for path in BLOBS} | {
        'SourceFlowPhysicalCarrierRepro.olean', 'SourceFlowPhysicalGreenRealSliceDraft.olean'} | {
        stage + '.log' for stage in queue}
    require(set(files) <= allowed, 'UNEXPECTED_FILE')
    if records:
        require(json.loads(files['records.json']) == records, 'ATOMIC_RECORDS')
    for index, record in enumerate(records):
        stage = record['stage']
        require(record['cwd'] == ROOT and record['command'] == queue[stage], 'COMMAND=' + stage)
        require(record['log'] == stage + '.log', 'LOG_NAME=' + stage)
        require(type(record['exit']) is int, 'EXIT_TYPE=' + stage)
        require(type(record['seconds']) in (float, int) and math.isfinite(record['seconds'])
                and record['seconds'] >= 0, 'DURATION=' + stage)
        require(sha(files[record['log']]) == record['sha256'], 'LOG_HASH=' + stage)
        require(record['exit'] == 0 or index == len(records)-1, 'CONTINUED_AFTER_ERROR')
    for path, digest in BLOBS.items():
        if Path(path).name in files:
            require(sha(files[Path(path).name]) == digest, 'SOURCE_BYTES=' + path)
    for name, digest in data['compiled_output_hashes'].items():
        require(name in ('SourceFlowPhysicalCarrierRepro.olean',
                         'SourceFlowPhysicalGreenRealSliceDraft.olean'), 'OUTPUT_NAME')
        require(sha(files[name]) == digest, 'OUTPUT_HASH=' + name)
    if data['status'] == 'PASS':
        require(len(records) == len(queue) and all(r['exit'] == 0 for r in records), 'PASS_EXITS')
        require(data['error'] is None, 'PASS_ERROR')
        require(files['retained_head.log'].decode().strip() == COLD_SOURCE, 'HEAD_LOG')
        require(files['mathlib_pin.log'].decode().strip() ==
                '07642720480157414db592fa85b626dafb71355b', 'MATHLIB_LOG')
        require(files['paths.txt'].decode().splitlines() == list(BLOBS), 'OVERLAY_PATHS')
        require(all(Path(path).name in files for path in BLOBS), 'MISSING_SOURCE')
        require(set(data['compiled_output_hashes']) == {
            'SourceFlowPhysicalCarrierRepro.olean', 'SourceFlowPhysicalGreenRealSliceDraft.olean'},
            'PASS_OUTPUT_SET')
        actual = gate.exact_axioms(files['physical_real_slice_draft.log'].decode(), EXPECTED)
        require(data['axioms'] == actual, 'AXIOM_MAP')
    else:
        require(isinstance(data['error'], str) and bool(data['error']), 'FAIL_WITHOUT_ERROR')
        if data['axioms']:
            require(any(r['stage'] == 'physical_real_slice_draft' and r['exit'] == 0
                        for r in records), 'AXIOMS_WITHOUT_SUCCESSFUL_CHILD')
            actual = gate.exact_axioms(files['physical_real_slice_draft.log'].decode(), EXPECTED)
            require(data['axioms'] == actual, 'FAILED_PREFIX_AXIOM_MAP')
    return dict(status=data['status'], cold_seal=False, source=SOURCE,
        stages=len(records), files=len(files), first_error=data['error'],
        public_axiom_count=len(data['axioms']))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--archive', type=Path, required=True)
    parser.add_argument('--sha256', required=True)
    parser.add_argument('--cold-sha256', required=True)
    parser.add_argument('--axiom-gate', type=Path, required=True)
    args = parser.parse_args()
    blob = args.axiom_gate.read_bytes()
    require(sha(blob) == HELPER_HASHES['full_green_owner_exact_axiom_gate.py'], 'GATE_HELPER_HASH')
    gate = types.ModuleType('verified_physical_real_slice_axiom_gate')
    exec(compile(blob, 'hash_pinned_axiom_gate', 'exec'), gate.__dict__)
    report = verify(read_archive(args.archive, args.sha256), args.cold_sha256.lower(), gate)
    report['archive_sha256'] = args.sha256.lower()
    print(json.dumps(report, sort_keys=True, indent=2))
    print('PHYSICAL_REAL_SLICE_HOT_PACKAGE_VERIFIED COLD_SEAL=0')


if __name__ == '__main__':
    main()
