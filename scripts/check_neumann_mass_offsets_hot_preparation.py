"""Measured static readiness check; templates deliberately cannot run yet."""
import ast
import hashlib
from pathlib import Path
import subprocess

rp = Path('tmp/colab_neumann_generated_mass_complete_offsets_hot_v1.py.template')
vp = Path('tmp/verify_neumann_generated_mass_complete_offsets_hot_v1.py.template')
rt, vt = rp.read_text(), vp.read_text()
ra, va = ast.parse(rt), ast.parse(vt)
def constants(tree):
    out = {}
    for node in tree.body:
        if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            try:
                out[node.targets[0].id] = ast.literal_eval(node.value)
            except (ValueError, TypeError):
                pass
    return out
r, v = constants(ra), constants(va)
assert r['SOURCE'] == v['SOURCE'] == '4a05bff83ac0a30a7bdced8b1adee45828aaef24'
assert r['BASE'] == v['BASE'] == '7f7455b286da5809a0ee64a1511684f887cf8a88'
assert r['REV'] == v['REV'] == 'neumann-generated-mass-complete-offsets-hot-v1'
assert r['PARENT_OUTER_SHA'] is None and v['RUNNER_HASH'] is None
main = next(n for n in ra.body if isinstance(n, ast.FunctionDef) and n.name == 'main')
assert isinstance(main.body[0], ast.Assert)
assert main.body[0].msg.value == 'PARENT_COLD_EVIDENCE_NOT_PINNED'
assert len(r['PINS']) == 6
for path, digest in r['PINS'].items():
    ref = r['BASE'] if path.startswith('YangMills/') else r['SOURCE']
    blob = subprocess.check_output(['git', 'cat-file', 'blob', ref + ':' + path], timeout=5)
    assert hashlib.sha256(blob).hexdigest() == digest, path
    if path.endswith('Draft.lean'):
        names = [x.removeprefix('#print axioms ') for x in blob.decode().splitlines()
                 if x.startswith('#print axioms ')]
        assert names == r['NAMES']['physical_draft'] and len(names) == 6
assert "'PHYSICAL_SCOPE'" in vt
assert rt.index("run('mathlib_repro'") < rt.index("run('physical_prerequisites'")
assert 'NeumannGeneratedMassCompleteOffsetsRepro.lean' in vt
assert 'NeumannGeneratedMassCompleteOffsetsDraft.lean' in vt
assert 'NeumannGeneratedCompleteFibreDraft.lean' not in rt + vt
assert 'neumann-average-field-cohort' not in rt + vt
assert rt.count("'FINAL_STATUS='") == 1
print('MASS_OFFSETS_HOT_PREPARATION=PASS BLOB_PINS=6 AUDIT_NAMES=6')
print('NOT_EXECUTABLE: parent cold archive hash and final runner hash still unfilled')
print('COMPILER_CHECKED=0')
