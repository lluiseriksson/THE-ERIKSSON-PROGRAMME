"""Synthetic adversarial fixtures ONLY; no compiler or claimed Lean evidence."""
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import types

sys.path.insert(0, 'scripts')
def sha(b):
    return hashlib.sha256(b).hexdigest()
final = True
rt = Path('scripts/colab_neumann_generated_mass_complete_offsets_hot_v2.py' if final else
          'tmp/colab_neumann_generated_mass_complete_offsets_hot_v2.py.template').read_text()
vt = Path('scripts/verify_neumann_generated_mass_complete_offsets_hot_v2.py' if final else
          'tmp/verify_neumann_generated_mass_complete_offsets_hot_v2.py.template').read_text()
if not final:
    assert rt.count('PARENT_OUTER_SHA = None') == vt.count('RUNNER_HASH = None') == 1
    rt = rt.replace('PARENT_OUTER_SHA = None', "PARENT_OUTER_SHA = '" + '1' * 64 + "'")
rb = rt.encode()
vt = vt.replace('RUNNER_HASH = None', 'RUNNER_HASH = ' + repr(sha(rb)))
r, v = types.ModuleType('synthetic_runner'), types.ModuleType('synthetic_reader')
exec(compile(rt, 'synthetic_runner', 'exec'), r.__dict__)
exec(compile(vt, 'synthetic_reader', 'exec'), v.__dict__)
files = {'runner.py': rb}
if final:
    assert v.RUNNER_HASH == sha(rb), 'FINAL_GIT_RUNNER_HASH'
    files['parent-reviewed-cold-evidence.json'] = subprocess.check_output(
        ['git', 'cat-file', 'blob', r.REVIEW_REF + ':' + r.REVIEW_PATH], timeout=5)
    assert sha(files['parent-reviewed-cold-evidence.json']) == r.REVIEW_HASH
for p, digest in r.PINS.items():
    files[Path(p).name] = subprocess.check_output(
        ['git', 'cat-file', 'blob', r.SOURCE_REFS[p] + ':' + p], timeout=5)
    assert sha(files[Path(p).name]) == digest
gate = types.ModuleType('synthetic_gate')
exec(compile(files['full_green_owner_exact_axiom_gate.py'], 'synthetic_gate', 'exec'), gate.__dict__)
commands = {
    'base_head': ['git', 'rev-parse', 'HEAD'],
    'mathlib_pin': ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'],
    'lean_version': ['lean', '--version'], 'lake_version': ['lake', '--version'],
    'clean_before': ['git', 'diff', '--exit-code', 'HEAD', '--', 'YangMills', 'lean-toolchain', 'lake-manifest.json'],
    'mathlib_repro': ['lake', 'env', 'lean', '-o', (r.OUT / 'mathlib_repro.olean').as_posix(),
        'tmp/' + r.REV + '/NeumannGeneratedMassCompleteOffsetsRepro.lean'],
    'physical_prerequisites': ['lake', 'build', 'YangMills.RG.NeumannGeneratedCompleteFibre',
        'YangMills.RG.NeumannGeneratedAverageFieldAction',
        'YangMills.RG.BalabanCMP99SourceFlatGeneratedQprimeDirectOwnerKernel'],
    'physical_draft': ['lake', 'env', 'lean', '-o', (r.OUT / 'physical_draft.olean').as_posix(),
        'tmp/' + r.REV + '/NeumannGeneratedMassCompleteOffsetsDraft.lean'],
    'clean_after': ['git', 'diff', '--exit-code', 'HEAD', '--', 'YangMills', 'lean-toolchain', 'lake-manifest.json'],
}
logs = {s: b'' for s in commands}
logs['base_head'] = (r.BASE + '\n').encode()
logs['mathlib_pin'] = b'07642720480157414db592fa85b626dafb71355b\n'
logs['lean_version'] = logs['lake_version'] = b'SYNTHETIC 4.29.0-rc6\n'
logs['physical_draft'] = '\n'.join("'YangMills.RG." + n +
    "' depends on axioms: [propext, Classical.choice, Quot.sound]"
    for n in r.NAMES['physical_draft']).encode()
records = []
for stage, command in commands.items():
    files[stage + '.log'] = logs[stage]
    records.append(dict(stage=stage, command=command, cwd=r.ROOT.as_posix(), exit=0,
        seconds=0.125, timed_out=False, timeout_seconds=600 if stage == 'physical_prerequisites' else 120,
        log_sha256=sha(logs[stage])))
for n in ('physical_draft.olean', 'mathlib_repro.olean'):
    files[n] = b'SYNTHETIC FIXTURE, NOT A LEAN OUTPUT'
for n in ('lean-sha256.txt', 'lake-sha256.txt'):
    files[n] = ('2' * 64 + '\n').encode()
data = dict(status='PASS', source=r.SOURCE, base_source=r.BASE, cold_seal=False,
    pins=r.PINS, source_refs=r.SOURCE_REFS, names=r.NAMES, records=records,
    axioms={'physical_draft': gate.exact_axioms(logs['physical_draft'].decode(),
        {'YangMills.RG.' + n for n in r.NAMES['physical_draft']})},
    outputs={n: sha(files[n]) for n in ('physical_draft.olean', 'mathlib_repro.olean')},
    parent_outer_sha256=r.PARENT_OUTER_SHA,
    scope='actual generated source-weighted/counting mass finite offsets and common integer image; not regional inverse, uniform B0 or window15')
if final:
    data.update(parent_review_sha256=r.REVIEW_HASH, parent_production_olean_sha256=r.PARENT_OLEAN_HASH)
def pack(fs, d):
    fs['result.json'] = (json.dumps(d, sort_keys=True) + '\n').encode()
    fs['records.json'] = (json.dumps(d['records'], sort_keys=True) + '\n').encode()
    return fs
assert v.verify(pack(copy.deepcopy(files), copy.deepcopy(data)))['status'] == 'VERIFIED_HOT_PASS'
bad = []
for key, value in [('source', 'wrong'), ('cold_seal', True), ('scope', 'regional inverse proved'),
                   ('parent_outer_sha256', '0' * 64)]:
    d = copy.deepcopy(data); d[key] = value
    bad.append(pack(copy.deepcopy(files), d))
d = copy.deepcopy(data); d['records'][5]['command'][-1] = 'wrong.lean'
bad.append(pack(copy.deepcopy(files), d))
d = copy.deepcopy(data); d['records'] = d['records'][:-1]
bad.append(pack(copy.deepcopy(files), d))
d = copy.deepcopy(data); d['records'][6]['exit'] = 1
bad.append(pack(copy.deepcopy(files), d))
f = copy.deepcopy(files); f['physical_draft.olean'] += b'corrupt'
bad.append(pack(f, copy.deepcopy(data)))
f = copy.deepcopy(files); f['unexpected.txt'] = b'extra'
bad.append(pack(f, copy.deepcopy(data)))
f, d = copy.deepcopy(files), copy.deepcopy(data)
f['physical_draft.log'] = f['physical_draft.log'].replace(b'Quot.sound', b'sorryAx')
d['records'][7]['log_sha256'] = sha(f['physical_draft.log'])
bad.append(pack(f, d))
for i, sample in enumerate(bad):
    try:
        v.verify(sample)
    except (ValueError, AssertionError):
        continue
    raise AssertionError('BAD_FIXTURE_ACCEPTED=' + str(i))
d = copy.deepcopy(data)
d['status'] = 'FAIL'; d['records'] = d['records'][:-1]; d['records'][-1]['exit'] = 1
assert v.verify(pack(copy.deepcopy(files), d))['status'] == 'VERIFIED_FAILURE'
print('MASS_OFFSETS_READER_SYNTHETIC_SELF_TEST=PASS valid=1 rejected=10 preserved_failure=1')
print('SYNTHETIC_ONLY COMPILER_CHECKED=0 ACTUAL_HOT_RESULT=NOT_RUN')
