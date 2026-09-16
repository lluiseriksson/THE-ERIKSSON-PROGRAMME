"""Instrument-only synthetic mutation tests; never mathematical evidence."""
import copy
import json
import subprocess
import types
from verify_neumann_finite_integer_kernel_hot_v2 import verify, SOURCE, BASE, REV, ROOT, sha


def blob(commit, path):
    return subprocess.check_output(['git', 'cat-file', 'blob', commit + ':' + path], timeout=5)


runner_bytes = blob('a3bbb0bbda604929bd57586e7387100c15021301', 'scripts/colab_neumann_finite_integer_kernel_hot_v2.py')
runner = types.ModuleType('runner')
exec(compile(runner_bytes, 'runner', 'exec'), runner.__dict__)
files = {'runner.py': runner_bytes}
for path in runner.PINS:
    files[path.rsplit('/', 1)[-1]] = blob(SOURCE, path)
gate = types.ModuleType('gate')
exec(compile(files['full_green_owner_exact_axiom_gate.py'], 'gate', 'exec'), gate.__dict__)
gate.self_test()
commands = [
    ('base_head', ['git', 'rev-parse', 'HEAD'], (BASE + '\n').encode()),
    ('mathlib_pin', ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'], b'07642720480157414db592fa85b626dafb71355b\n'),
    ('lean_version', ['lean', '--version'], b'Lean 4.29.0-rc6\n'),
    ('lake_version', ['lake', '--version'], b'Lake 4.29.0-rc6\n'),
]
clean = ['git', 'diff', '--exit-code', 'HEAD', '--', 'YangMills', 'lean-toolchain', 'lake-manifest.json']
commands.append(('clean_before', clean, b''))
axioms, outputs = {}, {}
for stage, name in [('mathlib_repro', 'NeumannFiniteIntegerCoordinatesMathlibRepro.lean'),
                    ('physical_draft', 'NeumannGeneratedIntegerCountingKernelDraft.lean')]:
    if stage == 'physical_draft':
        commands.append(('physical_prerequisites', ['lake', 'build', 'YangMills.RG.BalabanCMP99SourceFlatGeneratedQprimeDirectOwnerKernel'], b'SYNTHETIC TEST ONLY\n'))
    text = ''.join("'YangMills.RG." + n + "' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n" for n in runner.NAMES[stage])
    axioms[stage] = gate.exact_axioms(text, {'YangMills.RG.' + n for n in runner.NAMES[stage]})
    files[stage + '.olean'] = b'SYNTHETIC TEST ONLY, NOT A LEAN OUTPUT'
    outputs[stage + '.olean'] = sha(files[stage + '.olean'])
    commands.append((stage, ['lake', 'env', 'lean', '-o', '/content/' + REV + '-evidence/' + stage + '.olean', 'tmp/' + REV + '/' + name], text.encode()))
commands.append(('clean_after', clean, b''))
records = []
for stage, command, log in commands:
    files[stage + '.log'] = log
    records.append(dict(stage=stage, command=command, cwd=ROOT, exit=0, seconds=0.01,
        timed_out=False, timeout_seconds=3600 if stage == 'physical_prerequisites' else 120, log_sha256=sha(log)))
for exe in ('lean', 'lake'):
    files[exe + '-sha256.txt'] = ('0'*64 + '\n').encode()
data = dict(status='PASS', source=SOURCE, base_source=BASE, cold_seal=False,
    pins=runner.PINS, names=runner.NAMES, records=records, axioms=axioms, outputs=outputs)


def fixture(d):
    f = dict(files)
    f['result.json'] = json.dumps(d).encode()
    f['records.json'] = json.dumps(d['records']).encode()
    return f


good = fixture(data)
assert verify(good)['status'] == 'VERIFIED_HOT_PASS'
bad = []
for name in ('runner.py', 'NeumannFiniteIntegerCoordinatesMathlibRepro.lean',
             'NeumannGeneratedIntegerCountingKernelDraft.lean', 'physical_draft.log', 'physical_draft.olean'):
    f = dict(good)
    f[name] += b'corruption'
    bad.append(f)
for key, value in [('source', '0'*40), ('cold_seal', True), ('status', 'FAIL')]:
    d = copy.deepcopy(data)
    d[key] = value
    bad.append(fixture(d))
for field, value in [('exit', 1), ('timed_out', True), ('cwd', '/wrong'), ('seconds', float('nan')),
                     ('command', ['echo', 'PASS']), ('timeout_seconds', 9999)]:
    d = copy.deepcopy(data)
    d['records'][6][field] = value
    bad.append(fixture(d))
d = copy.deepcopy(data)
d['records'].pop()
bad.append(fixture(d))
d = copy.deepcopy(data)
d['records'].append(d['records'][-1])
bad.append(fixture(d))
for f in bad:
    try:
        verify(f)
    except (AssertionError, ValueError, KeyError):
        continue
    raise AssertionError('MUTATION_ACCEPTED')
print('INSTRUMENT_TEST_ONLY synthetic_pass=1 rejected=' + str(len(bad)))

# A real old failure must never become the new source's PASS by repackaging.
from pathlib import Path
from verify_neumann_counting_reflection_diagnostic_v2 import unpack
old = Path('validation-evidence/neumann-finite-integer-kernel-hot-v1-fail-20260906/neumann-finite-integer-kernel-hot-v1-evidence.tar.gz')
old_files = {name.split('/', 1)[1]: b for name, b in unpack(old.read_bytes()).items()}
try:
    verify(old_files)
except (AssertionError, ValueError, KeyError):
    print('REAL_V1_ARCHIVE_REJECTED_AS_V2=1')
else:
    raise AssertionError('OLD_FAILURE_ACCEPTED_AS_NEW_EVIDENCE')
