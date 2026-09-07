"""Verify/preserve a bounded HOT dictionary and its actual prior v2 archive.

No compiler, network or pool. Success is diagnostic only. A source operator
dictionary never becomes a regional inverse by passing this instrument.
"""
import argparse
import contextlib
import io
import json
import math
from pathlib import Path
import sys
import types

import verify_neumann_counting_reflection_diagnostic_v2 as v

SOURCE = '214b6923f3523d44282d5772fa6ab09782864f10'
BASE = '06a928178b22c42c4ecc5387461b808ee3a19dea'
TREE = 'd60f95120f11de18d0d3e3a73e90c9b59db07f05'
RUNNER = '483774c10b45d38de8fc40a79709207f1b73ea0dd26d765e2aa8db216d7c6538'
BLOB = '6f8a5be71b33261c263291b9049337ed068f1aee282f7eb1482b264bcd91e7f6'
PRIOR_VERIFIER = 'a596e50eb708d39819da3f15557fa5705ab564874b70d9913f8a8b9794bec851'
NAME = 'NeumannRetainedCountingMassDictionaryDraft.lean'
WORK = '/content/neumann-retained-counting-dictionary-hot-v1'
PRIOR_REMOTE = '/content/neumann-generated-counting-reflection-diagnostic-v2-preservation-20260906.tar.gz'
INPUT = 'tmp/neumann_retained_counting_dictionary_hot_v1/' + NAME
STAGES = ['verify_prior', 'base_head', 'production_tree', 'clean_source',
    'mathlib_pin', 'lean_version', 'lake_version', 'text_guard', 'import_guard',
    'prerequisites', 'retained_counting_dictionary', 'final_clean_source']
NAMES = {'YangMills.RG.neumannFlatGeneratedCountingMass_eq_explicit_draft',
    'YangMills.RG.neumannFlatRetainedTerminalCountingMass_eq_explicit_draft'}


def check(files, gate, prior_hash):
    data = json.loads(files['evidence.json'])
    for key, value in dict(status='PASS', cold_seal=False, base=BASE,
            source=SOURCE, source_blob=BLOB, production_tree=TREE,
            prior_sha256=prior_hash, error=None).items():
        v.require(data.get(key) == value, 'FIELD=' + key)
    expected_files = {'runner.py', NAME, 'records.json', 'paths.txt', 'draft.olean',
        'toolchain-binaries.json', 'full_green_owner_exact_axiom_gate.py',
        'verify_neumann_counting_reflection_diagnostic_v2.py',
        *(s + '.log' for s in STAGES)}
    v.require(set(data['files']) == expected_files, 'MANIFEST_SET')
    v.require(set(files) == expected_files | {'evidence.json'}, 'FILE_SET')
    for name, digest in data['files'].items():
        v.require(v.sha(files[name]) == digest, 'HASH=' + name)
    for name, digest in {'runner.py': RUNNER, NAME: BLOB,
            'full_green_owner_exact_axiom_gate.py': v.GATE_HASH,
            'verify_neumann_counting_reflection_diagnostic_v2.py': PRIOR_VERIFIER}.items():
        v.require(v.sha(files[name]) == digest, 'PIN=' + name)
    records = data['records']
    v.require(json.loads(files['records.json']) == records, 'RECORDS')
    v.require([r['stage'] for r in records] == STAGES, 'STAGE_ORDER')
    for r in records:
        v.require(r['exit'] == 0 and r['timed_out'] is False, 'CHILD=' + r['stage'])
        v.require(math.isfinite(r['seconds']) and r['seconds'] >= 0, 'TIMER')
        v.require(r['cwd'] == v.ROOT, 'CWD')
        v.require(v.sha(files[r['stage'] + '.log']) == r['log_sha256'], 'LOG=' + r['stage'])
    commands = {r['stage']: r['command'] for r in records}
    python = commands['verify_prior'][0]
    v.require(python in ('/usr/bin/python3', '/usr/local/bin/python3'), 'PYTHON')
    bindir = '/content/lean-4.29.0-rc6-linux/lean-4.29.0-rc6-linux/bin/'
    expected_commands = {
        'verify_prior': [python, WORK + '/verify_neumann_counting_reflection_diagnostic_v2.py',
            '--archive', PRIOR_REMOTE, '--sha256', prior_hash,
            '--axiom-helper', v.ROOT + '/scripts/full_green_owner_exact_axiom_gate.py'],
        'base_head': ['git', 'rev-parse', 'HEAD'],
        'production_tree': ['git', 'rev-parse', 'HEAD:YangMills'],
        'clean_source': ['git', 'diff', '--exit-code', 'HEAD', '--',
            'YangMills', 'lean-toolchain', 'lake-manifest.json'],
        'mathlib_pin': ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'],
        'lean_version': [bindir + 'lean', '--version'],
        'lake_version': [bindir + 'lake', '--version'],
        'text_guard': [python, 'scripts/check_lean_overlay_text.py', '--paths-from',
            WORK + '/paths.txt', '--require-prevalidation'],
        'import_guard': [python, 'scripts/check_lean_import_prefix.py', INPUT],
        'prerequisites': ['lake', 'build',
            'YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalPrecisionKernel',
            'YangMills.RG.BalabanCMP99SourceRetainedGeneratedTerminalBridge'],
        'retained_counting_dictionary': ['lake', 'env', 'lean', '-o', WORK + '/draft.olean', INPUT],
    }
    expected_commands['final_clean_source'] = expected_commands['clean_source']
    v.require(commands == expected_commands, 'COMMANDS')
    for name, value in [('base_head.log', BASE), ('production_tree.log', TREE),
            ('mathlib_pin.log', v.MATHLIB), ('paths.txt', INPUT)]:
        v.require(files[name].decode().strip() == value, 'VALUE=' + name)
    for name in ('lean_version.log', 'lake_version.log'):
        v.require('4.29.0-rc6' in files[name].decode(), 'VERSION=' + name)
    axioms = gate.exact_axioms(files['retained_counting_dictionary.log'].decode(), NAMES)
    v.require(axioms == data['axioms'], 'AXIOM_RECORD')
    v.require(len(files['draft.olean']) > 0, 'EMPTY_OUTPUT')
    return dict(status='PASS', cold_seal=False, source=SOURCE, base=BASE,
        prior_sha256=prior_hash, axioms=axioms, stages=len(records),
        output_sha256=v.sha(files['draft.olean']), records=records)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--archive', type=Path, required=True)
    p.add_argument('--sha256', required=True)
    p.add_argument('--prior', type=Path, required=True)
    p.add_argument('--axiom-helper', type=Path, required=True)
    p.add_argument('--destination', type=Path)
    a = p.parse_args()
    if a.destination is not None:
        v.require(not a.destination.exists(), 'NO_OVERWRITE')
    v.require(a.archive.stat().st_size <= 64 * 2**20, 'ARCHIVE_SIZE')
    v.require(a.prior.stat().st_size <= 64 * 2**20, 'PRIOR_SIZE')
    blob, prior = a.archive.read_bytes(), a.prior.read_bytes()
    v.require(v.sha(blob) == a.sha256.lower(), 'OUTER_HASH')
    nested = v.unpack(blob)
    prefix = Path(WORK).name + '/'
    v.require(all(n.startswith(prefix) for n in nested), 'ARCHIVE_PREFIX')
    files = {n[len(prefix):]: b for n, b in nested.items()}
    prior_hash = v.sha(prior)
    # Re-run the full independent prior verifier on the real archive supplied,
    # rather than treating the stored verify_prior.log as sufficient evidence.
    saved = sys.argv
    prior_output = io.StringIO()
    try:
        sys.argv = ['prior_verifier', '--archive', str(a.prior), '--sha256', prior_hash,
            '--axiom-helper', str(a.axiom_helper)]
        with contextlib.redirect_stdout(prior_output):
            v.main()
    finally:
        sys.argv = saved
    helper = a.axiom_helper.read_bytes()
    v.require(v.sha(helper) == v.GATE_HASH, 'HELPER')
    gate = types.ModuleType('pinned_gate')
    exec(compile(helper, str(a.axiom_helper), 'exec'), gate.__dict__)
    report = check(files, gate, prior_hash)
    report['outer_sha256'] = v.sha(blob)
    report['prior_verification_sha256'] = v.sha(prior_output.getvalue().encode())
    payload = (json.dumps(report, sort_keys=True, indent=2) + '\n').encode()
    if a.destination is not None:
        root = a.destination
        root.mkdir(parents=True, exist_ok=False)
        (root / a.archive.name).write_bytes(blob)
        for name, content in nested.items():
            target = root / Path(name)
            target.parent.mkdir(parents=True, exist_ok=True)
            with target.open('xb') as out:
                out.write(content)
        (root / 'independent-verification.json').write_bytes(payload)
        (root / 'prior-independent-verification.txt').write_text(prior_output.getvalue())
    print(payload.decode(), end='')
    print('RETAINED_COUNTING_DICTIONARY_HOT_VERIFIED COLD_SEAL=0')
    print('REPORT_SHA256=' + v.sha(payload))


if __name__ == '__main__':
    main()
