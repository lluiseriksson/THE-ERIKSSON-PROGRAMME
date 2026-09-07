"""Independent exact HOT archive check; no compiler/network/pools."""
import argparse
import json
import math
from pathlib import Path
import types
from verify_neumann_counting_reflection_diagnostic_v2 import unpack, sha, require

SOURCE = '93264d4b654022f51cd1d1f0ce7963de26408d4b'
BASE = 'eb5a9ec0609b015a3d367c0d729c2c2074a45b51'
REV = 'neumann-common-block-phase-hot-v1'
ROOT = '/content/hrpoly-neumann-actual-scalar-diagnostic-v1'
RUNNER_HASH = None  # pin only the finalized parent-reviewed runner


def verify(files):
    require(isinstance(RUNNER_HASH, str) and len(RUNNER_HASH) == 64, 'RUNNER_NOT_PINNED')
    require(sha(files['runner.py']) == RUNNER_HASH, 'RUNNER_HASH')
    runner = types.ModuleType('pinned_runner')
    exec(compile(files['runner.py'], 'pinned_runner', 'exec'), runner.__dict__)
    require(runner.SOURCE == SOURCE and runner.BASE == BASE and runner.REV == REV, 'PINNED_SOURCE')
    data = json.loads(files['result.json'])
    require(data['source'] == SOURCE and data['base_source'] == BASE and data['cold_seal'] is False, 'SOURCE_OR_SCOPE')
    require(data['parent_outer_sha256'] == runner.PARENT_OUTER_SHA, 'PARENT_ARCHIVE')
    require(data['scope'] == "common integer-block endpoint phases only; not full Green covariance, regional inverse, B0 or window15", 'PHYSICAL_SCOPE')
    require(data['parent_review_sha256'] == runner.REVIEW_HASH, 'PARENT_REVIEW_HASH')
    require(data['parent_production_olean_sha256'] == runner.PARENT_OLEAN_HASH, 'PARENT_OUTPUT')
    require(sha(files['parent-reviewed-diagnostic-evidence.json']) == runner.REVIEW_HASH, 'PARENT_REVIEW_FILE')
    review = json.loads(files['parent-reviewed-diagnostic-evidence.json'])
    require(review['status'] == 'VERIFIED_DIAGNOSTIC_PASS' and review['cold_seal'] is False and review['source'] == BASE, 'PARENT_REVIEW_STATUS')
    require(review['archive_sha256'] == runner.PARENT_OUTER_SHA, 'PARENT_ARCHIVE_REVIEW')
    require(review['outputs']['NeumannActualFullSolutionScalarDraft.olean'] == runner.PARENT_OLEAN_HASH, 'PARENT_OUTPUT_REVIEW')
    require(data['source_refs'] == runner.SOURCE_REFS, 'SOURCE_REFS')
    require(data['pins'] == runner.PINS and data['names'] == runner.NAMES, 'PINS_NAMES')
    for p, digest in runner.PINS.items():
        require(sha(files[Path(p).name]) == digest, 'INPUT=' + p)
    require(data['records'] == json.loads(files['records.json']), 'RECORDS')
    expected_stages = ['base_head', 'mathlib_pin', 'lean_version', 'lake_version',
        'clean_before', 'physical_prerequisites', 'physical_draft', 'clean_after']
    stages = [r['stage'] for r in data['records']]
    require(len(stages) == len(set(stages)), 'DUPLICATE_STAGE')
    require(stages == expected_stages[:len(stages)], 'STAGE_ORDER')
    require(files['base_head.log'].decode().strip() == BASE, 'BASE_HEAD')
    require(files['mathlib_pin.log'].decode().strip() == '07642720480157414db592fa85b626dafb71355b', 'MATHLIB')
    commands = {
        'base_head': ['git', 'rev-parse', 'HEAD'],
        'mathlib_pin': ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'],
        'lean_version': ['lean', '--version'],
        'lake_version': ['lake', '--version'],
    }
    commands['physical_prerequisites'] = ["lake","build","YangMills.RG.BalabanCMP89CenteredTorusGreenCoefficientPhase"]
    for s in ('clean_before', 'clean_after'):
        commands[s] = ['git', 'diff', '--exit-code', 'HEAD', '--', 'YangMills', 'lean-toolchain', 'lake-manifest.json']
    for s, name in [('physical_draft', 'NeumannCommonBlockEndpointPhaseDraft.lean')]:
        commands[s] = ['lake', 'env', 'lean', '-o', '/content/' + REV + '-evidence/' + s + '.olean',
                       'tmp/' + REV + '/' + name]
    for r in data['records']:
        s = r['stage']
        require(r['command'] == commands[s], 'COMMAND=' + s)
        require(type(r['exit']) is int and type(r['timed_out']) is bool, 'EXIT_TYPE')
        require(sha(files[s + '.log']) == r['log_sha256'], 'LOG=' + s)
        require(r['cwd'] == ROOT and math.isfinite(r['seconds']) and r['seconds'] >= 0, 'CWD_TIME')
        require(r['timeout_seconds'] == (600 if s == 'physical_prerequisites' else 120), 'TIMEOUT_BUDGET')
    require(data['status'] in ('PASS', 'FAIL'), 'STATUS')
    if data['status'] == 'FAIL':
        # Preserve first real failure, never count a successful prefix as a seal.
        nonzero = [r for r in data['records'] if r['exit'] != 0 or r['timed_out']]
        require(len(nonzero) == 1 and nonzero[0] == data['records'][-1], 'FIRST_FAILURE')
        return dict(status='VERIFIED_FAILURE', cold_seal=False, source=SOURCE,
            failed_stage=nonzero[0], log=files[nonzero[0]['stage'] + '.log'].decode())
    require(stages == expected_stages, 'MISSING_STAGE')
    require(all(r['exit'] == 0 and r['timed_out'] is False for r in data['records']), 'CHILD_FAILURE')
    require(files['clean_before.log'] == files['clean_after.log'] == b'', 'SOURCE_DIRTY')
    for exe in ('lean', 'lake'):
        require('4.29.0-rc6' in files[exe + '_version.log'].decode(), 'TOOLCHAIN')
    gate = types.ModuleType('pinned_gate')
    exec(compile(files['full_green_owner_exact_axiom_gate.py'], 'pinned_gate', 'exec'), gate.__dict__)
    require(set(data['axioms']) == set(runner.NAMES), 'AXIOM_STAGE_SET')
    require(set(data['outputs']) == {'physical_draft.olean'}, 'OUTPUT_SET')
    expected_files = {'parent-reviewed-diagnostic-evidence.json', 'runner.py', 'records.json', 'result.json', 'lean-sha256.txt', 'lake-sha256.txt',
        *(Path(p).name for p in runner.PINS), *(s + '.log' for s in stages), *data['outputs']}
    require(set(files) == expected_files, 'FILE_SET')
    for s, path in [('physical_draft', 'tmp/NeumannCommonBlockEndpointPhaseDraft.lean')]:
        r = next(r for r in data['records'] if r['stage'] == s)
        require(r['command'] == ['lake', 'env', 'lean', '-o', '/content/' + REV + '-evidence/' + s + '.olean', 'tmp/' + REV + '/' + Path(path).name], 'COMMAND=' + s)
        require(data['axioms'][s] == gate.exact_axioms(files[s + '.log'].decode(), {'YangMills.RG.' + n for n in runner.NAMES[s]}), 'AXIOMS')
    for n, digest in data['outputs'].items():
        require(files[n] and sha(files[n]) == digest, 'OUTPUT=' + n)
    return dict(status='VERIFIED_HOT_PASS', cold_seal=False, source=SOURCE,
        records=data['records'], axioms=data['axioms'], outputs=data['outputs'])


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--archive', type=Path, required=True)
    p.add_argument('--sha256', required=True)
    p.add_argument('--destination', type=Path)
    a = p.parse_args()
    require(a.archive.stat().st_size < 32*2**20, 'SIZE')
    blob = a.archive.read_bytes()
    require(sha(blob) == a.sha256.lower(), 'ARCHIVE_HASH')
    raw = unpack(blob)
    prefix = REV + '-evidence/'
    require(all(n.startswith(prefix) and '/' not in n[len(prefix):] for n in raw), 'PREFIX')
    files = {n[len(prefix):]: b for n, b in raw.items()}
    report = verify(files)
    report['archive_sha256'] = sha(blob)
    payload = (json.dumps(report, indent=2, sort_keys=True) + '\n').encode()
    if a.destination:
        require(not a.destination.exists(), 'NO_OVERWRITE')
        a.destination.mkdir()
        (a.destination / a.archive.name).write_bytes(blob)
        for n, b in files.items():
            (a.destination / n).write_bytes(b)
        (a.destination / 'independent-verification.json').write_bytes(payload)
    print(payload.decode())
    print('VERIFIED_REPORT_SHA256=' + sha(payload))


if __name__ == '__main__':
    main()
