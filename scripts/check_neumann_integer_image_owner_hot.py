"""Static instrument checks only; no compiler, child process, network or pool."""
import ast
import copy
import hashlib
import json
from pathlib import Path
import runpy

path = Path('scripts/colab_neumann_integer_image_owner_hot.py')
tree = ast.parse(path.read_text())
values = {n.targets[0].id: ast.literal_eval(n.value) for n in tree.body
    if isinstance(n, ast.Assign) and isinstance(n.targets[0], ast.Name)
    and isinstance(n.value, (ast.Constant, ast.Set, ast.Dict))}
assert values['BASE'] == '9b73a5fe37d1e5e3c8589af211c46708a9d0a7bb'
assert values['SOURCE'] == 'd7e2199934a14c843d46cb08094c554bc9d0c5f1'
assert values['BLOB'] == '62c8ceb7502820740147bd678955e0ca529cceb6954bb350b4c0fbbcfc46a4d1'
assert len(values['NAMES']) == 3
repro = Path('tmp/NeumannIntegerImageBlockOwnerRepro.lean').read_text()
assert {line.removeprefix('#print axioms ') for line in repro.splitlines()
    if line.startswith('#print axioms ')} == values['NAMES']
assert all(line.startswith('import Mathlib.') for line in repro.splitlines()
    if line.startswith('import '))
assert 'PRE-VALIDATION:' in repro
calls = [n for n in ast.walk(tree) if isinstance(n, ast.Call)
    and isinstance(n.func, ast.Name) and n.func.id == 'run']
literal_stages = {n.args[0].value: n for n in calls if isinstance(n.args[0], ast.Constant)}
assert 'verify_cold_archive' in literal_stages
assert 'integer_image_owner_repro' in literal_stages
assert 'prerequisites' not in literal_stages
lean = literal_stages['integer_image_owner_repro']
assert [ast.literal_eval(e) for e in lean.args[1].elts[:3]] == ['lake', 'env', 'lean']
assert next(ast.literal_eval(k.value) for k in lean.keywords if k.arg == 'timeout') == 120
assert not any(isinstance(n, ast.Constant) and n.value in ('build', 'checkout', 'update')
    for n in ast.walk(tree))
assert 'cold_seal=False' in path.read_text()
verifier_path = Path('scripts/verify_neumann_integer_image_owner_hot.py')
verifier = runpy.run_path(str(verifier_path), run_name='instrument_check')
for key in ('BASE', 'SOURCE', 'BLOB', 'NAME', 'NAMES', 'PINS'):
    assert verifier[key] == values[key], 'VERIFIER_DRIFT=' + key
# Commit-derived runner hash is fixed separately; do not derive the reference
# from a CRLF worktree read. Its value was measured with binary git cat-file.
assert verifier['RUNNER'] == '5089ed064f0ad30556c2bda35576f661a8db6e8f62eb71a288ffdaf007313b8d'
prior = b'synthetic-not-a-prior-archive'
base = dict(status='PASS', cold_seal=False, base=values['BASE'],
    source=values['SOURCE'], source_blob=values['BLOB'],
    prior_sha256=hashlib.sha256(prior).hexdigest(), error=None)
for field, bad in [('status', 'FAIL'), ('cold_seal', True), ('base', 'bad'),
        ('source', 'bad'), ('source_blob', 'bad'), ('prior_sha256', 'bad'), ('error', 'bad')]:
    data = copy.deepcopy(base)
    data[field] = bad
    try:
        verifier['check']({'evidence.json': json.dumps(data).encode()}, prior)
    except ValueError as error:
        assert str(error) == 'FIELD=' + field
    else:
        raise AssertionError('BAD_FIELD_ACCEPTED=' + field)
print('VERIFIER_PIN_CONSISTENCY=PASS NEGATIVE_FIELDS=7 ACTUAL_PASS_NOT_YET_TESTED=1')
print('INTEGER_IMAGE_OWNER_HOT_STATIC=PASS MATHLIB_ONLY=1 LEAN_CHILDREN=1 COMPILER_EVIDENCE=0')
