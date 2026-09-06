"""Static instrument checks only; no compiler, child process, network or pool."""
import ast
from pathlib import Path

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
print('INTEGER_IMAGE_OWNER_HOT_STATIC=PASS MATHLIB_ONLY=1 LEAN_CHILDREN=1 COMPILER_EVIDENCE=0')
