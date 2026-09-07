"""Lightweight cold-instrument checks; no compiler/network/subprocess/pool."""
import ast
import json
from pathlib import Path
import runpy
import sys

runner = ast.parse(Path('scripts/colab_neumann_integer_dictionary_cohort_cold.py').read_text())
verifier = ast.parse(Path('scripts/verify_neumann_integer_dictionary_cohort_cold.py').read_text())

def literal_assignment(tree, name):
    values = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if ast.unparse(target) == name:
                    try:
                        values.append(ast.literal_eval(node.value))
                    except (ValueError, TypeError):
                        pass
    assert len(values) == 1, 'LITERAL_COUNT=' + name
    return values[0]

assert literal_assignment(runner, 'SOURCE') == literal_assignment(verifier, 'SOURCE')
assert literal_assignment(runner, 'runner.SOURCE_BLOBS') == literal_assignment(verifier, 'BLOBS')
assert literal_assignment(runner, 'audit_names') == literal_assignment(verifier, 'NAMES')
names = literal_assignment(verifier, 'NAMES')
commands = literal_assignment(verifier, 'COMMANDS')
assert len(literal_assignment(verifier, 'BLOBS')) == 4
assert sum(map(len, names.values())) == 11
assert list(commands) == ['counting_focal', 'counting_audit', 'interval_focal', 'interval_audit']
queue = next(n.value for n in ast.walk(runner) if isinstance(n, ast.Assign)
    and any(ast.unparse(t) == 'runner.QUEUE' for t in n.targets))
assert [ast.literal_eval(n.elts[0]) for n in queue.elts] == list(commands)
for n in queue.elts:
    assert ast.literal_eval(n.elts[1]) == commands[ast.literal_eval(n.elts[0])]
print('PINNED_SOURCE_BLOBS_NAMES_QUEUE=PASS files=4 names=11')
launcher = ast.parse(Path('scripts/launch_neumann_integer_dictionary_cohort_cold.py').read_text())
preserver = ast.parse(Path('scripts/preserve_verify_neumann_integer_dictionary_cohort_cold.py').read_text())
nb = json.loads(Path('scripts/colab_neumann_integer_dictionary_cohort_cold.ipynb').read_text())
cells = [c for c in nb['cells'] if c['cell_type'] == 'code']
assert len(cells) == 1 and cells[0]['execution_count'] is None and cells[0]['outputs'] == []
code = ''.join(cells[0]['source'])
cell = ast.parse(code)
assert literal_assignment(cell, 'SOURCE_SHA') == literal_assignment(runner, 'SOURCE')
assert literal_assignment(cell, 'RUNNER_REV') == literal_assignment(launcher, 'REV')
assert literal_assignment(cell, 'LAUNCHER_SHA256') == literal_assignment(preserver, 'LAUNCHER_HASH')
assert code.count('SOURCE_SHA =') == code.count('RUNNER_REV =') == 1
assert '59160603' not in code and 'halfcell' not in code
files_node = next(n.value for n in ast.walk(launcher) if isinstance(n, ast.Assign)
    and any(ast.unparse(t) == 'FILES' for t in n.targets))
source = literal_assignment(runner, 'SOURCE')
class SourceLiteral(ast.NodeTransformer):
    def visit_Name(self, node):
        return ast.Constant(source) if node.id == 'SOURCE' else node
files = ast.literal_eval(SourceLiteral().visit(files_node))
pins_node = next(n.value for n in ast.walk(preserver) if isinstance(n, ast.Assign)
    and any(ast.unparse(t) == 'PINS' for t in n.targets))
assert files == ast.literal_eval(SourceLiteral().visit(pins_node))
print('ONE_CELL_LAUNCHER_PRESERVER_PINS=PASS')
check = runpy.run_path('scripts/preserve_verify_neumann_integer_dictionary_cohort_cold.py', run_name='instrument_test')
sys.argv = ['preserver', '--archive',
    'validation-evidence/neumann-counting-reflection-diagnostic-v2-20260906/neumann-generated-counting-reflection-diagnostic-v2-preservation-20260906.tar.gz',
    '--outer-sha256', 'ed2cda8e2fac4c51a1d49b140b5956fd0ba05134b9e0f2dddf4c1fecfa522d92']
try:
    check['main']()
except ValueError as error:
    assert str(error) == 'OUTER_FILES', 'WRONG_NEGATIVE_FAILURE'
else:
    raise AssertionError('WRONG_DIAGNOSTIC_ACCEPTED_AS_COLD')
print('REAL_DIAGNOSTIC_ARCHIVE_REJECTED_AS_COLD=PASS')
script = 'scripts/verify_neumann_integer_dictionary_cohort_cold.py'
sys.argv = [script, '--helpers',
    'validation-evidence/neumann-halfcell-reflection-cold-20260905/neumann-halfcell-block-reflection-cold-v1-launch',
    '--self-test']
runpy.run_path(script, run_name='__main__')
print('COLD_INSTRUMENT_STATIC_TESTS=PASS COMPILER_EVIDENCE=0')
