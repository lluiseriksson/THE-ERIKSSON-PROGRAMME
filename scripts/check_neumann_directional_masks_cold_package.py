"""Pin/transport/notebook checks only; no network, compiler or new evidence."""
import ast
import hashlib
import json
from pathlib import Path
import runpy
import subprocess
import sys
import types

sys.path.insert(0,'scripts')
import launch_neumann_directional_masks_promoted_cold as launch
import preserve_neumann_directional_masks_cold as preserve
import verify_neumann_directional_masks_promoted_cold as reader

assert launch.SOURCE == preserve.SOURCE == reader.SOURCE == '74fc4f4dcd115558de6cf882d17540fe57d9bd27'
assert launch.REV == preserve.REV == reader.REV == 'neumann-directional-masks-promoted-cold-v1'
assert launch.FILES == preserve.PINS
for name,(ref,digest) in launch.FILES.items():
    blob=subprocess.check_output(['git','cat-file','blob',ref+':scripts/'+name],timeout=5)
    assert hashlib.sha256(blob).hexdigest()==digest,name

nb=json.loads(Path('scripts/colab_neumann_directional_masks_promoted_cold.ipynb').read_text())
code_cells=[c for c in nb['cells'] if c['cell_type']=='code']
assert len(code_cells)==1 and code_cells[0]['execution_count'] is None and code_cells[0]['outputs']==[]
code=''.join(code_cells[0]['source'])
tree=ast.parse(code)
constants={n.targets[0].id:ast.literal_eval(n.value) for n in tree.body
    if isinstance(n,ast.Assign) and isinstance(n.targets[0],ast.Name) and isinstance(n.value,ast.Constant)}
assert constants['SOURCE_SHA']==launch.SOURCE and constants['RUNNER_REV']==launch.REV
assert code.count('SOURCE_SHA =')==code.count('RUNNER_REV =')==1
assert '7f7455b286da5809a0ee64a1511684f887cf8a88' not in code
ref='2fde75090c4d98f6617bcaa88e12320d9c2c76eb'
name='launch_neumann_directional_masks_promoted_cold.py'
blob=subprocess.check_output(['git','cat-file','blob',ref+':scripts/'+name],timeout=5)
assert hashlib.sha256(blob).hexdigest()==constants['LAUNCHER_SHA256']==preserve.LAUNCHER_HASH
assert constants['url']==launch.RAW+ref+'/scripts/'+name
assert code.count('subprocess.Popen(')==1
assert code.index('TRANSPORT_HASH')<code.index('subprocess.Popen(')
assert launch.OUTER.as_posix() in code and preserve.LAUNCHER==name
assert launch.INNER.as_posix()=='/content/hrpoly-'+launch.REV+'-evidence.tar.gz'
runpy.run_path('scripts/test_neumann_directional_masks_cold_preparation.py',run_name='__main__')
print('DIRECTIONAL_MASKS_COLD_PACKAGE=PASS LAUNCHER_HASH=1 TRANSPORTS=4 CODE_CELLS=1')
print('COMPILER_CHECKED=0 EXECUTION_NOT_STARTED=1')
