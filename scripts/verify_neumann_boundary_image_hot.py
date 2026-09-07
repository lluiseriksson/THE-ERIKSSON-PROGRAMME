"""Independent bounded-orbit evidence reader. No compiler or subprocess calls."""
import argparse
import hashlib
import json
import math
from pathlib import Path
import types

SOURCE = '7f7c6915a691d1b97bc53cfd695a978874e40a8e'
BASE = '108f30f954e3d807f16c4264fac56f4814c65ea4'
PIN = 'bf51447da311b0d6e98bc8286000418d40ad52721d3674dac2c493a654c596b7'
RUNNER = 'ce37b29b4ade2a3ae6abc2efad975b244e65422ba78c2220eb1beaf4827c652a'
REV = 'neumann-boundary-image-hot-v1'
ROOT = '/content/hrpoly-neumann-boundary-orbit-diagnostic-v2'
NAMES = {'YangMills.RG.neumannBoundaryImageIndexEquiv_involutive',
         'YangMills.RG.neumannBoundaryImageIndexEquiv_image'}
COMMANDS = {
    'head': ['git', 'rev-parse', 'HEAD'],
    'mathlib': ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'],
    'clean_before': ['git', 'diff', '--exit-code', 'HEAD', '--', 'YangMills', 'lean-toolchain', 'lake-manifest.json'],
    'lean_version': ['lean', '--version'],
    'lake_version': ['lake', '--version'],
    'orbit': ['lake', 'env', 'lean', '-o', '/content/'+REV+'/orbit.olean',
        'tmp/'+REV+'/NeumannBoundaryImagePermutationDraft.lean'],
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
    require(sha(files['NeumannBoundaryImagePermutationDraft.lean']) == PIN, 'SOURCE_HASH')
    require(json.loads(files['parent-review.json']) == parent, 'PARENT_REVIEW')
    records = data['records']
    require([r['stage'] for r in records] == list(COMMANDS), 'STAGE_SET_ORDER')
    expected_files = {'runner.py', 'result.json', 'parent-review.json',
        'NeumannBoundaryImagePermutationDraft.lean', 'orbit.olean'}
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
    ap.add_argument('--parent-archive', type=Path, required=True)
    ap.add_argument('--parent-sha256', required=True)
    ap.add_argument('--archive', type=Path, required=True)
    ap.add_argument('--sha256', required=True)
    args = ap.parse_args()
    import verify_neumann_boundary_orbit_diagnostic as parent_reader
    from verify_neumann_counting_reflection_diagnostic_v2 import unpack
    raw = args.parent_archive.read_bytes()
    require(sha(raw)==args.parent_sha256.lower(), 'PARENT_ARCHIVE_HASH')
    prefix = 'hrpoly-neumann-boundary-orbit-diagnostic-v2-evidence/'
    contents = unpack(raw)
    require(all(n.startswith(prefix) for n in contents), 'PARENT_PREFIX')
    parent_files = {n[len(prefix):]:v for n,v in contents.items()}
    parent = parent_reader.verify(parent_files)
    gate = types.ModuleType('verified_gate')
    exec(compile(parent_files['axiom-gate.py'], 'verified_gate', 'exec'), gate.__dict__)
    raw = args.archive.read_bytes()
    require(sha(raw)==args.sha256.lower(), 'ARCHIVE_HASH')
    contents = unpack(raw)
    prefix=REV+'/'
    require(all(n.startswith(prefix) and '/' not in n[len(prefix):] for n in contents), 'PREFIX')
    files={n[len(prefix):]:v for n,v in contents.items()}
    report = verify(files, parent, args.parent_sha256, gate)
    report['archive_sha256'] = args.sha256.lower()
    print(json.dumps(report, sort_keys=True, indent=2))
    print('BOUNDARY_IMAGE_HOT_EVIDENCE_VERIFIED')

if __name__ == '__main__': main()


