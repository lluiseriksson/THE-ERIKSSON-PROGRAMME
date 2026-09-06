"""Static pin/source/name check only. No compiler, network, pools."""
import ast
import hashlib
import runpy
import subprocess
from pathlib import Path
from verify_neumann_counting_reflection_diagnostic_v2 import unpack
from verify_neumann_generated_average_field_action_hot_v2 import verify, RUNNER_HASH
p = 'scripts/colab_neumann_generated_average_field_action_hot_v2.py'
b = subprocess.check_output(['git','cat-file','blob','4c96c6ce611eeee9e1f57900197f38180a8392d6:'+p],timeout=5)
assert hashlib.sha256(b).hexdigest() == RUNNER_HASH
r = runpy.run_path(p,run_name='instrument_only')
f = {p: subprocess.check_output(['git','cat-file','blob',r['SOURCE']+':'+p],timeout=5) for p in r['PINS']}
for p,b in f.items(): assert hashlib.sha256(b).hexdigest() == r['PINS'][p]
draft = f['tmp/NeumannGeneratedAverageFieldActionDraft.lean'].decode()
assert [l.removeprefix('#print axioms YangMills.RG.') for l in draft.splitlines() if l.startswith('#print axioms ')] == r['NAMES']['physical_draft']
assert len(r['NAMES']['physical_draft']) == 3
old = Path('validation-evidence/neumann-actual-full-green-images-hot-v1-20260906/neumann-actual-full-green-images-hot-v1-evidence.tar.gz').read_bytes()
try: verify({n.split('/',1)[1]:b for n,b in unpack(old).items()})
except ValueError as e: assert str(e) == 'RUNNER_HASH'
else: raise AssertionError('OLD_GREEN_ACCEPTED')
assert len(f) == 4
print('FIELD_ACTION_INSTRUMENTS=PASS inputs=' + str(len(f)) + ' names=3 old_archive_rejected=1 NO_COMPILER_EVIDENCE')
