"""Lightweight cold-instrument checks; no compiler/network/subprocess/pool."""
import ast
from pathlib import Path
import runpy
import sys

runner = ast.parse(Path('scripts/colab_neumann_counting_promoted_cold.py').read_text())
verifier = ast.parse(Path('scripts/verify_neumann_counting_promoted_cold.py').read_text())

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
assert sum(map(len, names.values())) == 5
assert list(commands) == ['reflection_focal', 'reflection_audit', 'dictionary_focal', 'dictionary_audit']
queue = next(n.value for n in ast.walk(runner) if isinstance(n, ast.Assign)
    and any(ast.unparse(t) == 'runner.QUEUE' for t in n.targets))
assert [ast.literal_eval(n.elts[0]) for n in queue.elts] == list(commands)
for n in queue.elts:
    assert ast.literal_eval(n.elts[1]) == commands[ast.literal_eval(n.elts[0])]
print('PINNED_SOURCE_BLOBS_NAMES_QUEUE=PASS files=4 names=5')
script = 'scripts/verify_neumann_counting_promoted_cold.py'
sys.argv = [script, '--helpers',
    'validation-evidence/neumann-halfcell-reflection-cold-20260905/neumann-halfcell-block-reflection-cold-v1-launch',
    '--self-test']
runpy.run_path(script, run_name='__main__')
print('COLD_INSTRUMENT_STATIC_TESTS=PASS COMPILER_EVIDENCE=0')
