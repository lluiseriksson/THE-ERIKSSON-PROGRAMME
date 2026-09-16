"""Synthetic adversarial fixtures ONLY; no compiler or claimed Lean evidence."""
import copy
import ast
import hashlib
import json
import re
from pathlib import Path, PurePosixPath
import subprocess
import sys
import types

sys.path.insert(0, 'scripts')
def sha(b):
    return hashlib.sha256(b).hexdigest()
rt = Path('tmp/colab_neumann_rectangle_flat_masked_action_hot_template.py').read_text()
vt = Path('tmp/verify_neumann_rectangle_flat_masked_action_hot_template.py').read_text()
for key in ('PARENT_OUTER_SHA', 'REVIEW_REF', 'REVIEW_HASH', 'PARENT_OLEAN_HASH'):
    assert rt.count(key + ' = None') == 1, key
assert vt.count('RUNNER_HASH = None') == 1
r0 = types.ModuleType('not_ready_runner')
exec(compile(rt, 'not_ready_runner', 'exec'), r0.__dict__)
try:
    r0.main()
except AssertionError as e:
    assert str(e) == 'PARENT_COLD_EVIDENCE_NOT_PINNED'
else:
    raise AssertionError('UNPINNED_RUNNER_DID_NOT_STOP')
parent = dict(status='VERIFIED_COLD_PASS', source=r0.BASE, cold_seal=True,
    outer_sha256='1'*64, cold=dict(status='PASS', source_sha=r0.BASE,
    production_outputs={'NeumannRectangleDirectionalMasks.olean': '3'*64}))
parent_blob = (json.dumps(parent, sort_keys=True)+'\n').encode()
for key, value in dict(PARENT_OUTER_SHA='1'*64, REVIEW_REF='2'*40,
    REVIEW_HASH=sha(parent_blob), PARENT_OLEAN_HASH='3'*64).items():
    rt = rt.replace(key + ' = None', key + ' = ' + repr(value))
rb = rt.encode()
vt = vt.replace('RUNNER_HASH = None', 'RUNNER_HASH = ' + repr(sha(rb)))
r, v = types.ModuleType('synthetic_runner'), types.ModuleType('synthetic_reader')
exec(compile(rt, 'synthetic_runner', 'exec'), r.__dict__)
exec(compile(vt, 'synthetic_reader', 'exec'), v.__dict__)
files = {'runner.py': rb, 'parent-reviewed-cold-evidence.json': parent_blob}
for p, digest in r.PINS.items():
    files[Path(p).name] = subprocess.check_output(
        ['git', 'cat-file', 'blob', r.SOURCE_REFS[p] + ':' + p], timeout=5)
    assert sha(files[Path(p).name]) == digest
draft = files['NeumannRectangleFlatMaskedActionDraft.lean'].decode()
audited = re.findall(r'^#print axioms (\w+)\s*$', draft, re.M)
declared = re.findall(r'^theorem (\w+)', draft, re.M)
assert audited == declared == r.NAMES['physical_draft'], 'ACTUAL_SOURCE_AUDIT_NAMES'
imports = re.findall(r'^import (\S+)', draft, re.M)
assert set(imports) == {p[:-5].replace('/', '.') for p in r.PINS if p.startswith('YangMills/')}, 'ACTUAL_IMPORT_PINS'
gate = types.ModuleType('synthetic_gate')
exec(compile(files['full_green_owner_exact_axiom_gate.py'], 'synthetic_gate', 'exec'), gate.__dict__)
commands = {
    'base_head': ['git', 'rev-parse', 'HEAD'],
    'mathlib_pin': ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'],
    'lean_version': ['lean', '--version'], 'lake_version': ['lake', '--version'],
    'clean_before': ['git', 'diff', '--exit-code', 'HEAD', '--', 'YangMills', 'lean-toolchain', 'lake-manifest.json'],
    'physical_prerequisites': ["lake","build","YangMills.RG.NeumannRectangleDirectionalMasks","YangMills.RG.NeumannFlatInternalBondAction"],
    'physical_draft': ['lake', 'env', 'lean', '-o', (r.OUT / 'physical_draft.olean').as_posix(),
        'tmp/' + r.REV + '/NeumannRectangleFlatMaskedActionDraft.lean'],
    'clean_after': ['git', 'diff', '--exit-code', 'HEAD', '--', 'YangMills', 'lean-toolchain', 'lake-manifest.json'],
}
# Check the producer actually emits the commands modelled by the reader.
tree = ast.parse(rt)
main_node = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'main')
calls = [n for n in ast.walk(main_node) if isinstance(n, ast.Call)
    and isinstance(n.func, ast.Name) and n.func.id == 'run']
assert len(calls) == 7, 'ACTUAL_RUN_CALL_COUNT'
root = PurePosixPath(r.ROOT.as_posix())
env = dict(Path=PurePosixPath, str=str, ROOT=root, scratch=root/'tmp'/r.REV)
literal = {}
for call in calls:
    if isinstance(call.args[0], ast.Constant):
        stage = call.args[0].value
        literal[stage] = eval(compile(ast.Expression(call.args[1]), '<actual command>', 'eval'), env)
        assert {k.arg:ast.literal_eval(k.value) for k in call.keywords} == (
            {'timeout':600} if stage == 'physical_prerequisites' else {})
assert literal == {s:commands[s] for s in (
    'base_head','mathlib_pin','clean_before','physical_prerequisites','clean_after')}
loops = [n for n in ast.walk(main_node) if isinstance(n,ast.For)
    and isinstance(n.target,ast.Tuple)
    and [e.id for e in n.target.elts if isinstance(e,ast.Name)] == ['stage','path']]
assert len(loops) == 1
assert ast.literal_eval(loops[0].iter) == [('physical_draft','NeumannRectangleFlatMaskedActionDraft.lean')]
draft_call = next(n for n in ast.walk(loops[0]) if isinstance(n,ast.Call)
    and isinstance(n.func,ast.Name) and n.func.id == 'run')
env.update(op=PurePosixPath(r.OUT.as_posix())/'physical_draft.olean',
    path='NeumannRectangleFlatMaskedActionDraft.lean')
assert eval(compile(ast.Expression(draft_call.args[1]),'<draft command>','eval'),env) == commands['physical_draft']
print('ACTUAL_RUNNER_AST_CONTRACT=PASS calls=7 expanded_stages=8 PROJECT_COMPOSITION=1')

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
for n in ('physical_draft.olean',):
    files[n] = b'SYNTHETIC FIXTURE, NOT A LEAN OUTPUT'
for n in ('lean-sha256.txt', 'lake-sha256.txt'):
    files[n] = ('2' * 64 + '\n').encode()
data = dict(status='PASS', source=r.SOURCE, base_source=r.BASE, cold_seal=False,
    pins=r.PINS, source_refs=r.SOURCE_REFS, names=r.NAMES, records=records,
    axioms={s: gate.exact_axioms(logs[s].decode(), {'YangMills.RG.' + n for n in ns}) for s,ns in r.NAMES.items()},
    outputs={n: sha(files[n]) for n in ('physical_draft.olean',)},
    parent_outer_sha256=r.PARENT_OUTER_SHA,
    scope='literal flat rectangular Laplacian with directional full-period masks; not integer boundary identification, physical carrier choice, reflection covariance, regional inverse, uniform B0 or window15')
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
d = copy.deepcopy(data); d['records'][5]['exit'] = 1
bad.append(pack(copy.deepcopy(files), d))
f = copy.deepcopy(files); f['physical_draft.olean'] += b'corrupt'
bad.append(pack(f, copy.deepcopy(data)))
f = copy.deepcopy(files); f['unexpected.txt'] = b'extra'
bad.append(pack(f, copy.deepcopy(data)))
f, d = copy.deepcopy(files), copy.deepcopy(data)
f['physical_draft.log'] = f['physical_draft.log'].replace(b'Quot.sound', b'sorryAx')
d['records'][6]['log_sha256'] = sha(f['physical_draft.log'])
bad.append(pack(f, d))
f, d = copy.deepcopy(files), copy.deepcopy(data)
f['physical_draft.log'] = f['physical_draft.log'].replace(b'Quot.sound', b'Other.axiom')
d['records'][6]['log_sha256'] = sha(f['physical_draft.log'])
bad.append(pack(f, d))
for i, sample in enumerate(bad):
    try:
        v.verify(sample)
    except (ValueError, AssertionError):
        continue
    raise AssertionError('BAD_FIXTURE_ACCEPTED=' + str(i))

# Audit coverage must be exact even if the archive's own hashes are updated.
extra_bad = []
d = copy.deepcopy(data); d['axioms']['unrequested_stage'] = {}
extra_bad.append(pack(copy.deepcopy(files), d))
for replacement in (b'', b"'YangMills.RG.wrongName' depends on axioms: [propext, Classical.choice, Quot.sound]"):
    f, d = copy.deepcopy(files), copy.deepcopy(data)
    f['physical_draft.log'] = replacement
    d['records'][6]['log_sha256'] = sha(replacement)
    extra_bad.append(pack(f, d))
for sample in extra_bad:
    try:
        v.verify(sample)
    except (ValueError, AssertionError):
        continue
    raise AssertionError('AUDIT_COVERAGE_MUTATION_ACCEPTED')
d = copy.deepcopy(data)
d['status'] = 'FAIL'; d['records'] = d['records'][:-1]; d['records'][-1]['exit'] = 1
assert v.verify(pack(copy.deepcopy(files), d))['status'] == 'VERIFIED_FAILURE'
print('MASKED_ACTION_TEMPLATE_SYNTHETIC_SELF_TEST=PASS valid=1 rejected=11 preserved_failure=1')
print('EXACT_AUDIT_COVERAGE_REJECTIONS=3')
print('SYNTHETIC_ONLY COMPILER_CHECKED=0 ACTUAL_HOT_RESULT=NOT_RUN')
