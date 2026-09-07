"""Exact flat v1-to-v2 delta; no Lean/network."""
import ast,hashlib,subprocess,runpy
from pathlib import Path
runpy.run_path('scripts/test_neumann_flat_internal_bond_action_hot_actual.py',run_name='__main__')
old='9838cd3c3c280971ef69fcf2e0bf19f4f193923c'
new='deea786e397c603179f1d573331eadc785c0947d'
def blob(r,p): return subprocess.check_output(['git','cat-file','blob',r+':'+p],timeout=5)
p='tmp/NeumannFlatInternalBondActionDraft.lean'
before=blob(old,p)
after=blob(new,p)
assert before.replace(b'cmp99SourceFlatGaugeConfig_apply, inv_one',b'cmp99SourceFlatGaugeConfig, inv_one')==after
assert hashlib.sha256(after).hexdigest()=='aafe9b691e99f85d2bd7e2b82cde149cbf6ba7567d09b8c4210bd9402cb9981d'
def norm(s): return ast.dump(ast.parse(s))
r=Path('scripts/colab_neumann_flat_internal_bond_action_hot.py').read_text().replace(old,new).replace('neumann-flat-internal-bond-action-hot-v1','neumann-flat-internal-bond-action-hot-v2').replace('2478c299b924fb9976c6976d442fe3c2725b6ca5ea6f08178d196e4050c90c99','aafe9b691e99f85d2bd7e2b82cde149cbf6ba7567d09b8c4210bd9402cb9981d')
assert norm(r)==norm(Path('scripts/colab_neumann_flat_internal_bond_action_hot_v2.py').read_text())
v=Path('scripts/verify_neumann_flat_internal_bond_action_hot.py').read_text().replace(old,new).replace('neumann-flat-internal-bond-action-hot-v1','neumann-flat-internal-bond-action-hot-v2').replace('82f4b8b4bd7a1e8a79975dd850b5da25142768779ab9b15902bdb30158165745','9f5cd4e2aeb3abefb4d6f4bed615495337dc40678754fdde5fd6163aa25ddfcc')
assert norm(v)==norm(Path('scripts/verify_neumann_flat_internal_bond_action_hot_v2.py').read_text())
assert hashlib.sha256(blob('','scripts/colab_neumann_flat_internal_bond_action_hot_v2.py')).hexdigest()=='9f5cd4e2aeb3abefb4d6f4bed615495337dc40678754fdde5fd6163aa25ddfcc'
print('FLAT_V2_EXACT_ONE_LINE_DELTA_PASS COMPILER_CHECKED=0')
