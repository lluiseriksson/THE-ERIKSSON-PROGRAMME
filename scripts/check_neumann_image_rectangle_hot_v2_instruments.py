"""Bounded textual/pin checks. No Lean, no network, no compilation evidence."""
import ast
import hashlib
from pathlib import Path
import subprocess
import types


def sha(b):
    return hashlib.sha256(b).hexdigest()


def load(path):
    b = Path(path).read_bytes()
    ast.parse(b)
    module = types.ModuleType('instrument_only')
    exec(compile(b, path, 'exec'), module.__dict__)
    return module


runner_path = 'scripts/colab_neumann_image_rectangle_hot_v2.py'
runner = load(runner_path)
verifier = load('scripts/verify_neumann_image_rectangle_hot_v2.py')
assert runner.SOURCE == verifier.SOURCE == 'fbf2e61f38afbe050200a0c7aa275b46ae45a924'
assert runner.BASE == verifier.BASE == 'af35fbb8c75bf2347543034b3abf27f0217b1bbf'
assert runner.REV == verifier.REV == 'neumann-image-rectangle-hot-v2'
assert len(runner.PINS) == 8
assert len({Path(p).name for p in runner.PINS}) == 8
assert len(runner.PARENT_OUTER_SHA) == 64, 'PARENT_COLD_NOT_VERIFIED'
assert sha(subprocess.check_output(['git', 'cat-file', 'blob', 'HEAD:' + runner_path], timeout=5)) == verifier.RUNNER_HASH
files = {}
for p, digest in runner.PINS.items():
    ref = runner.SOURCE if p == 'tmp/NeumannImageRectangleCoverageDraft.lean' else runner.SUPPORT_SOURCE
    b = subprocess.check_output(['git', 'cat-file', 'blob', ref + ':' + p], timeout=5)
    assert sha(b) == digest, 'BLOB=' + p
    files[p] = b
contract = types.ModuleType('pinned_repro_contract')
exec(compile(files['scripts/neumann_image_rectangle_repro_contract.py'], 'contract', 'exec'), contract.__dict__)
repro = contract.make_repro(files)
assert sha(repro) == '44b702e431a8d20fbcb5115a510bf721e32d1260a0b7e90c5cf839860881978f'
assert runner.NAMES == {'mathlib_repro': contract.NAMES, 'physical_draft': contract.NAMES}
assert b'import YangMills.' not in repro
assert len(contract.NAMES) == 5
old_path = Path('validation-evidence/neumann-image-interval-hot-v3-20260906/neumann-image-interval-hot-v3-evidence.tar.gz')
old = {n.split('/', 1)[1]: b for n, b in verifier.unpack(old_path.read_bytes()).items()}
try:
    verifier.verify(old)
except ValueError as e:
    assert str(e) == 'RUNNER_HASH'
else:
    raise AssertionError('OLD_INTERVAL_ACCEPTED_AS_RECTANGLE')
print('RECTANGLE_HOT_INSTRUMENTS=PASS files=8 names=5 old_archive_rejected=1')
print('COMPILER_EVIDENCE=0')
