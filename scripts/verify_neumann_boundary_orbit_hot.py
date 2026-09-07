"""Independent bounded-orbit evidence reader. No compiler or subprocess calls."""
import argparse
import hashlib
import json
import math
from pathlib import Path
import types

SOURCE = '108f30f954e3d807f16c4264fac56f4814c65ea4'
BASE = '84ceb5f2f466ab8f4e9dea175fd412c7bf63a21e'
PIN = '8abe85a4e6bf901cb300026018d81e8ff93b7d78ae5ce1a39932d4436322b3e9'
RUNNER = '23911a054a6db74e113c487313d7e2fd6ee95d9b60c11f061428b139f2310c41'
REV = 'neumann-boundary-orbit-hot-v1'
ROOT = '/content/hrpoly-neumann-physical-reflection-promoted-cold-v1'
NAMES = {'YangMills.RG.neumannBoundaryOrbitIndexEquiv_involutive',
         'YangMills.RG.neumannBoundaryOrbitIndexEquiv_image'}
COMMANDS = {
    'head': ['git', 'rev-parse', 'HEAD'],
    'mathlib': ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'],
    'clean_before': ['git', 'diff', '--exit-code', 'HEAD', '--', 'YangMills', 'lean-toolchain', 'lake-manifest.json'],
    'lean_version': ['lean', '--version'],
    'lake_version': ['lake', '--version'],
    'orbit': ['lake', 'env', 'lean', '-o', '/content/'+REV+'/orbit.olean',
        'tmp/'+REV+'/NeumannBoundaryOrbitPermutationRepro.lean'],
    'clean_after': ['git', 'diff', '--exit-code', 'HEAD', '--', 'YangMills', 'lean-toolchain', 'lake-manifest.json']}

def sha(b): return hashlib.sha256(b).hexdigest()
def require(ok, message):
    if not ok: raise ValueError(message)

def verify(files, parent, parent_hash, gate):
    data = json.loads(files['result.json'])
    for key, expected in dict(status='PASS', error=None, source=SOURCE, base=BASE,
            pin=PIN, revision=REV, cold_seal=False, names=sorted(NAMES),
            parent_archive_sha256=parent_hash.lower()).items():
        require(data.get(key) == expected, 'RESULT='+key)
    require(sha(files['runner.py']) == RUNNER, 'RUNNER_HASH')
    require(sha(files['NeumannBoundaryOrbitPermutationRepro.lean']) == PIN, 'SOURCE_HASH')
    require(json.loads(files['parent-review.json']) == parent, 'PARENT_REVIEW')
    records = data['records']
    require([r['stage'] for r in records] == list(COMMANDS), 'STAGE_SET_ORDER')
    expected_files = {'runner.py', 'result.json', 'parent-review.json',
        'NeumannBoundaryOrbitPermutationRepro.lean', 'orbit.olean'}
    for r in records:
        stage = r['stage']
        require(r['command'] == COMMANDS[stage] and r['cwd'] == ROOT, 'COMMAND='+stage)
        require(r['exit'] == 0 and r['timed_out'] is False and
            r['timeout_seconds'] == 120, 'EXIT_TIMEOUT='+stage)
        require(math.isfinite(r['seconds']) and r['seconds'] >= 0, 'TIME='+stage)
        require(sha(files[stage+'.log']) == r['log_sha256'], 'LOG_HASH='+stage)
        require(json.loads(files[stage+'.json']) == r, 'RECORD='+stage)
        expected_files |= {stage+'.log', stage+'.json'}
    require(set(files) == expected_files, 'FILE_SET')
    require(files['head.log'].decode().strip() == BASE, 'HEAD')
    require(files['mathlib.log'].decode().strip() == '07642720480157414db592fa85b626dafb71355b', 'MATHLIB')
    for exe in ('lean', 'lake'):
        require('4.29.0-rc6' in files[exe+'_version.log'].decode(), 'VERSION='+exe)
    audits = gate.exact_axioms(files['orbit.log'].decode(), NAMES)
    require(audits == data['audits'], 'AUDITS')
    require(data['outputs'] == {'orbit.olean': sha(files['orbit.olean'])}, 'OUTPUTS')
    return dict(status='PASS', cold_seal=False, source=SOURCE, base=BASE,
        parent_archive_sha256=parent_hash.lower(), audits=audits,
        output_sha256=sha(files['orbit.olean']), records=records)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--helpers', type=Path, required=True)
    ap.add_argument('--parent-archive', type=Path, required=True)
    ap.add_argument('--parent-sha256', required=True)
    ap.add_argument('--archive', type=Path, required=True)
    ap.add_argument('--sha256', required=True)
    args = ap.parse_args()
    b = (args.helpers/'verify_neumann_physical_reflection_promoted_cold.py').read_bytes()
    require(sha(b) == 'c0d54f929d54f4d52ff94019f09ab3b9c70160755c8969b1a11faa0933985787', 'COLD_READER_HASH')
    cold = types.ModuleType('cold')
    exec(compile(b, 'cold', 'exec'), cold.__dict__)
    old = cold.helper(args.helpers, 'verify_cmp99_full_green_residue_cold.py',
        '558295bb43e74bdae3eb6508656e7b8cde756cb393376320d0c197347396a02c')
    gate = cold.helper(args.helpers, 'full_green_owner_exact_axiom_gate.py', cold.GATE_HASH)
    old.PREFIX = 'hrpoly-'+cold.REV+'-evidence'
    parent = cold.verify(old.read_archive(args.parent_archive, args.parent_sha256), gate, old)
    old.PREFIX = REV
    files = old.read_archive(args.archive, args.sha256)
    report = verify(files, parent, args.parent_sha256, gate)
    report['archive_sha256'] = args.sha256.lower()
    print(json.dumps(report, sort_keys=True, indent=2))
    print('BOUNDARY_ORBIT_HOT_EVIDENCE_VERIFIED')

if __name__ == '__main__': main()
