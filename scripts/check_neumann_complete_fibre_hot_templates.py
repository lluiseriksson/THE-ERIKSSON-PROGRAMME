"""Static preparation gate; no compiler, network or child process."""
import ast
from pathlib import Path

runner_text = Path('tmp/colab_neumann_generated_complete_fibre_hot_v1.py.in').read_text(encoding='utf-8')
reader_text = Path('tmp/verify_neumann_generated_complete_fibre_hot_v1.py.in').read_text(encoding='utf-8')
runner = ast.parse(runner_text)
reader = ast.parse(reader_text)


def value(tree, name):
    found = [n.value for n in ast.walk(tree) if isinstance(n, ast.Assign)
             and any(ast.unparse(t) == name for t in n.targets)]
    assert len(found) == 1, 'ASSIGNMENT=' + name
    return ast.literal_eval(found[0])


for key, expected in (
    ('SOURCE', '8c07d3f3ccc833a38b7e6b6fd95764dd0985db63'),
    ('BASE', '8570618f20c62c5724555589f910b84fdf803c33'),
    ('REV', 'neumann-generated-complete-fibre-hot-v1'),
):
    assert value(runner, key) == value(reader, key) == expected, key
pins = value(runner, 'PINS')
names = value(runner, 'NAMES')['physical_draft']
assert len(pins) == 7 and len(names) == len(set(names)) == 6
draft = Path('tmp/NeumannGeneratedCompleteFibreDraft.lean').read_text(encoding='utf-8')
assert [l.removeprefix('#print axioms ') for l in draft.splitlines()
        if l.startswith('#print axioms ')] == names
assert runner_text.count('@PARENT_COLD_OUTER_SHA256@') == 1
assert reader_text.count('@FINAL_RUNNER_SHA256@') == 1
assert 'neumann-average-field-cohort-cold-v1-launch/launch-final-status.json' in runner_text
assert 'neumann-integer-dictionary-cohort-cold-v1' not in runner_text + reader_text
assert 'NeumannGeneratedAverageFieldActionDraft' not in runner_text + reader_text
run_calls = [n for n in ast.walk(runner) if isinstance(n, ast.Call)
    and isinstance(n.func, ast.Name) and n.func.id == 'run' and n.args
    and isinstance(n.args[0], ast.Constant)]
prereq = [n for n in run_calls if n.args[0].value == 'physical_prerequisites']
assert len(prereq) == 1
command = ast.literal_eval(prereq[0].args[1])
expected = ['lake', 'build', *[p[:-5].replace('/', '.') for p in pins if p.startswith('YangMills/')]]
assert command == expected == value(reader, "commands['physical_prerequisites']")
assert value(reader, 'expected_stages') == [
    'base_head', 'mathlib_pin', 'lean_version', 'lake_version', 'clean_before',
    'mathlib_repro', 'physical_prerequisites', 'physical_draft', 'clean_after']
compile(runner_text, 'runner-template', 'exec')
compile(reader_text, 'reader-template', 'exec')
print('HOT_TEMPLATE_SOURCE_BASE_NAMES_QUEUE=PASS inputs=7 names=6')
print('UNFINALIZED=1 WAIT_FOR_VERIFIED_PARENT_HASH=1 COMPILER_CHECKED=0')
