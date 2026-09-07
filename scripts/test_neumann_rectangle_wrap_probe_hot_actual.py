"""Actual pinned wrap HOT vs tested template and preserved cold review. No Lean/network."""
import ast
import hashlib
import json
from pathlib import Path
import runpy
import subprocess
import types

runpy.run_path('scripts/test_neumann_rectangle_wrap_probe_hot_template.py', run_name='__main__')
runner = types.ModuleType('actual_runner')
text = Path('scripts/colab_neumann_rectangle_wrap_probe_hot.py').read_text()
exec(compile(text, 'actual_runner', 'exec'), runner.__dict__)
review = subprocess.check_output(['git','cat-file','blob',runner.REVIEW_REF+':'+runner.REVIEW_PATH],timeout=5)
assert hashlib.sha256(review).hexdigest()==runner.REVIEW_HASH
data=json.loads(review)
assert data['status']=='VERIFIED_COLD_PASS' and data['source']==runner.BASE
assert data['outer_sha256']==runner.PARENT_OUTER_SHA
assert data['cold']['production_outputs']=={'NeumannInternalBondStencil.olean':runner.PARENT_OLEAN_HASH}
expected=Path('tmp/colab_neumann_rectangle_wrap_probe_hot_template.py').read_text()
for key in ('PARENT_OUTER_SHA','REVIEW_REF','REVIEW_HASH','PARENT_OLEAN_HASH'):
    expected=expected.replace(key+' = None',key+' = '+repr(getattr(runner,key)))
def normalized(s):
    tree=ast.parse(s)
    if isinstance(tree.body[0],ast.Expr) and isinstance(tree.body[0].value,ast.Constant):
        tree.body=tree.body[1:]
    return ast.dump(tree)
assert normalized(text)==normalized(expected),'ACTUAL_RUNNER_TEMPLATE_DRIFT'
blob=subprocess.check_output(['git','cat-file','blob','e8d513b2af902fb91b58bdb61c1f989de6e6440d:scripts/colab_neumann_rectangle_wrap_probe_hot.py'],timeout=5)
digest=hashlib.sha256(blob).hexdigest()
expected_reader=Path('tmp/verify_neumann_rectangle_wrap_probe_hot_template.py').read_text().replace('RUNNER_HASH = None','RUNNER_HASH = '+repr(digest))
assert normalized(Path('scripts/verify_neumann_rectangle_wrap_probe_hot.py').read_text())==normalized(expected_reader),'ACTUAL_READER_TEMPLATE_DRIFT'
print('ACTUAL_WRAP_HOT_PARENT_AND_TEMPLATE=PASS COMPILER_CHECKED=0')
