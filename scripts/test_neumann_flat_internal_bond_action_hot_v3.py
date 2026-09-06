"""Exact flat v2-to-v3 phase-order delta; no Lean/network."""
import ast,hashlib,subprocess,runpy
from pathlib import Path
runpy.run_path('scripts/test_neumann_flat_internal_bond_action_hot_actual.py',run_name='__main__')
old='deea786e397c603179f1d573331eadc785c0947d'
new='69a5308c8e5635b95b59c6d5c88d4b5b789f851c'
def blob(r,p): return subprocess.check_output(['git','cat-file','blob',r+':'+p],timeout=5)
p='tmp/NeumannFlatInternalBondActionDraft.lean'
before=blob(old,p).decode()
after=blob(new,p).decode()
oldproof='  simp only [neumannFlatInternalBond_extendedDerivative_apply,\n    cmp99SourceFlatGaugeConfig, inv_one,\n    SUNAdjointModel.ad_one_apply, FinBox.shift_shiftBack]'
newproof='  simp only [neumannFlatInternalBond_extendedDerivative_apply, FinBox.shift_shiftBack]\n  simp only [cmp99SourceFlatGaugeConfig, inv_one, SUNAdjointModel.ad_one_apply]'
assert before.count(oldproof)==1 and before.replace(oldproof,newproof)==after
assert hashlib.sha256(after.encode()).hexdigest()=='60198d54bcc958826af53ccd9c48aa2004bd00a0f5a818ddf7e7adfbf56ca694'
def norm(s): return ast.dump(ast.parse(s))
r=Path('scripts/colab_neumann_flat_internal_bond_action_hot_v2.py').read_text().replace(old,new).replace('neumann-flat-internal-bond-action-hot-v2','neumann-flat-internal-bond-action-hot-v3').replace('aafe9b691e99f85d2bd7e2b82cde149cbf6ba7567d09b8c4210bd9402cb9981d','60198d54bcc958826af53ccd9c48aa2004bd00a0f5a818ddf7e7adfbf56ca694')
assert norm(r)==norm(Path('scripts/colab_neumann_flat_internal_bond_action_hot_v3.py').read_text())
v=Path('scripts/verify_neumann_flat_internal_bond_action_hot_v2.py').read_text().replace(old,new).replace('neumann-flat-internal-bond-action-hot-v2','neumann-flat-internal-bond-action-hot-v3').replace('9f5cd4e2aeb3abefb4d6f4bed615495337dc40678754fdde5fd6163aa25ddfcc','cf61580acfc907227e4dad3a7a122cf9c68f79f50a6cab36dcd2ce8026b080d2')
assert norm(v)==norm(Path('scripts/verify_neumann_flat_internal_bond_action_hot_v3.py').read_text())
assert hashlib.sha256(blob('','scripts/colab_neumann_flat_internal_bond_action_hot_v3.py')).hexdigest()=='cf61580acfc907227e4dad3a7a122cf9c68f79f50a6cab36dcd2ce8026b080d2'
print('FLAT_V3_EXACT_PHASE_ORDER_DELTA_PASS COMPILER_CHECKED=0')
