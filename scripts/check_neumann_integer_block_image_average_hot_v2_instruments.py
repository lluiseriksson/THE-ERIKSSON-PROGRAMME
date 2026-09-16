"""Bounded exact Git-blob/repro/reader contract checks, not Lean evidence."""
import ast
import hashlib
import runpy
import subprocess
from pathlib import Path
from verify_neumann_counting_reflection_diagnostic_v2 import unpack
from verify_neumann_integer_block_image_average_hot_v2 import verify, RUNNER_HASH
runner_path = 'scripts/colab_neumann_integer_block_image_average_hot_v2.py'
blob = subprocess.check_output(['git', 'cat-file', 'blob', 'cf905d318fcc28a11ab56417cc117155f7958ca4:' + runner_path], timeout=5)
assert hashlib.sha256(blob).hexdigest() == RUNNER_HASH
r = runpy.run_path(runner_path, run_name='instrument_only')
f = {p: subprocess.check_output(['git','cat-file','blob',r['SOURCE']+':'+p], timeout=5) for p in r['PINS']}
for p,b in f.items():
    assert hashlib.sha256(b).hexdigest() == r['PINS'][p], p
c = runpy.run_path('scripts/neumann_integer_block_image_average_repro_contract.py',run_name='instrument_only')
repro = c['make_repro'](f)
assert hashlib.sha256(repro).hexdigest() == 'a71771253badcf3e43f42bcb567c63f84726975c6c64610fb026363a0ba3a555'
assert r['NAMES']['mathlib_repro'] == r['NAMES']['physical_draft'] == c['NAMES']
assert len(c['NAMES']) == 3
old = Path('validation-evidence/neumann-image-rectangle-hot-v2-20260906/neumann-image-rectangle-hot-v2-evidence.tar.gz').read_bytes()
try:
    verify({n.split('/',1)[1]:b for n,b in unpack(old).items()})
except ValueError as e:
    assert str(e) == 'RUNNER_HASH'
else:
    raise AssertionError('OLD_RECTANGLE_ACCEPTED')
print('BLOCK_IMAGE_AVERAGE_INSTRUMENTS=PASS inputs=' + str(len(f)) + ' names=3 old_archive_rejected=1 NO_COMPILER_EVIDENCE')

