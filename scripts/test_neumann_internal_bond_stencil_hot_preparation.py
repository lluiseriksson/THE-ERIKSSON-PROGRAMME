"""Actual HOT producer/reader must be exact instantiations of tested templates."""
import hashlib
from pathlib import Path
import runpy
import subprocess
import sys
sys.path.insert(0,'scripts')
pins = {"PARENT_OUTER_SHA":"33830a24341b533cff91184a3e0967f6ce5f1e23654c6fbccf584bd7e23f485d","REVIEW_REF":"fc28cbb63274fbe71e6cae88fed5d464aa6efdba","REVIEW_HASH":"ff717adf491d3403d767a74e8ddaca70c6a0c39578bbe2ad84a61ab370bd0e50","PARENT_OLEAN_HASH":"dbda0bf9590ece51553179d34eb947ceb5e543faba9333c11c938768da8020a2"}
template = subprocess.check_output(['git','cat-file','blob','d65d65c9ca8631dcb32a93ba540cf6076dcfd381:tmp/colab_neumann_internal_bond_stencil_hot_template.py'],timeout=5).decode()
for key,value in pins.items():
    assert template.count(key+' = None') == 1
    template = template.replace(key+' = None',key+' = '+repr(value))
template = template.replace('# Deliberately unset: only actual independently preserved parent-cold evidence may fill these.','# Actual independently preserved cold1164 pins; source and mathematical statements unchanged.')
actual = subprocess.check_output(['git','cat-file','blob','e15a6c288eb2702d7412039f74c0d8d79edb21d0:scripts/colab_neumann_internal_bond_stencil_hot.py'],timeout=5)
assert actual.decode() == template
digest = hashlib.sha256(actual).hexdigest()
assert digest == '6894d5bcfedebfda7427e6596883a7fa43cb45a025ad2347437fb484449428ac'
v = subprocess.check_output(['git','cat-file','blob','d65d65c9ca8631dcb32a93ba540cf6076dcfd381:tmp/verify_neumann_internal_bond_stencil_hot_template.py'],timeout=5).decode()
assert Path('scripts/verify_neumann_internal_bond_stencil_hot.py').read_text(encoding='utf8') == v.replace('RUNNER_HASH = None','RUNNER_HASH = '+repr(digest))
review = subprocess.check_output(['git','cat-file','blob',pins['REVIEW_REF']+':validation-evidence/neumann-canonical-spacing-cold-20260906/independent-local-verification.json'],timeout=5)
assert hashlib.sha256(review).hexdigest() == pins['REVIEW_HASH']
runpy.run_path('scripts/test_neumann_internal_bond_stencil_hot_template.py',run_name='__main__')
print('ACTUAL_BOND_HOT_TEMPLATE_INSTANTIATION=PASS COMPILER_CHECKED=0')
