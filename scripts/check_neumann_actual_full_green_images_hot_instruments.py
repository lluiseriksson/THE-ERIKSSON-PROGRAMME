"""Bounded static transport/statement gate; no Lean or network."""
import ast
import hashlib
from pathlib import Path
import subprocess
import types

def sha(b):
    return hashlib.sha256(b).hexdigest()

def module(b):
    ast.parse(b)
    m = types.ModuleType('instrument_only')
    exec(compile(b, 'pinned', 'exec'), m.__dict__)
    return m

path = 'scripts/colab_neumann_actual_full_green_images_hot_v1.py'
runner_bytes = subprocess.check_output(['git', 'cat-file', 'blob', 'HEAD:' + path], timeout=5)
r = module(runner_bytes)
v = module(Path('scripts/verify_neumann_actual_full_green_images_hot_v1.py').read_bytes())
assert sha(runner_bytes) == v.RUNNER_HASH
assert r.SOURCE == v.SOURCE and r.BASE == v.BASE and r.REV == v.REV
assert len(r.PINS) == 4
for p, h in r.PINS.items():
    b = subprocess.check_output(['git', 'cat-file', 'blob', r.SOURCE + ':' + p], timeout=5)
    assert sha(b) == h, p
    if p.startswith('YangMills/'):
        assert b == subprocess.check_output(['git', 'cat-file', 'blob', r.BASE + ':' + p], timeout=5)
    if p.startswith('tmp/'):
        names = [s.removeprefix('#print axioms YangMills.RG.') for s in b.decode().splitlines() if s.startswith('#print axioms ')]
        assert r.NAMES == {'physical_draft': names} and len(names) == 3
        assert 'cmp89Eq248PhysicalFullLatticeGreen' not in b.decode()
old = Path('validation-evidence/neumann-image-rectangle-hot-v2-20260906/neumann-image-rectangle-hot-v2-evidence.tar.gz')
f = {n.split('/', 1)[1]: b for n, b in v.unpack(old.read_bytes()).items()}
try:
    v.verify(f)
except ValueError as e:
    assert str(e) == 'RUNNER_HASH'
else:
    raise AssertionError('RECTANGLE_NOT_FULL_GREEN')
print('ACTUAL_FULL_GREEN_HOT_INSTRUMENTS=PASS pinned_files=4 names=3 compiler_evidence=0')
