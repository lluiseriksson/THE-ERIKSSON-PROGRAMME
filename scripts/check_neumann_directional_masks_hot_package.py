"""Exact template instantiation and real parent pins; no compiler/network."""
import hashlib
import json
from pathlib import Path
import runpy
import subprocess
import sys
import types

sys.path.insert(0, 'scripts')
def blob(ref, path):
    return subprocess.check_output(['git', 'cat-file', 'blob', ref + ':' + path], timeout=5)

def sha(b):
    return hashlib.sha256(b).hexdigest()

runner_ref = '919135cbf96ef03fbeaaff7688de46634c143fa0'
rb = blob(runner_ref, 'scripts/colab_neumann_rectangle_directional_masks_hot.py')
r = types.ModuleType('pinned_runner')
exec(compile(rb, 'pinned_runner', 'exec'), r.__dict__)
expected = Path('tmp/colab_neumann_rectangle_directional_masks_hot_template.py').read_text()
for key in ('PARENT_OUTER_SHA', 'REVIEW_REF', 'REVIEW_HASH', 'PARENT_OLEAN_HASH'):
    assert expected.count(key + ' = None') == 1, key
    expected = expected.replace(key + ' = None', key + ' = ' + repr(getattr(r, key)))
assert rb.decode() == expected, 'RUNNER_TEMPLATE_DRIFT'
vb = Path('scripts/verify_neumann_rectangle_directional_masks_hot.py').read_text()
vt = Path('tmp/verify_neumann_rectangle_directional_masks_hot_template.py').read_text()
assert vb == vt.replace('RUNNER_HASH = None', 'RUNNER_HASH = ' + repr(sha(rb))), 'READER_TEMPLATE_DRIFT'
compile(vb, 'actual_reader', 'exec')
review_blob = blob(r.REVIEW_REF, r.REVIEW_PATH)
assert sha(review_blob) == r.REVIEW_HASH, 'PARENT_REVIEW_BLOB'
review = json.loads(review_blob)
assert review['status'] == 'VERIFIED_COLD_PASS' and review['cold_seal'] is True
assert review['source'] == r.BASE and review['cold']['source_sha'] == r.BASE
assert review['outer_sha256'] == r.PARENT_OUTER_SHA
assert review['cold']['production_outputs']['NeumannRectangleWrapProbe.olean'] == r.PARENT_OLEAN_HASH
archive_path = str(Path(r.REVIEW_PATH).parent / 'neumann-wrap-flat-promoted-cold-v1-preservation-20260907.tar.gz').replace('\\', '/')
assert sha(blob(r.REVIEW_REF, archive_path)) == r.PARENT_OUTER_SHA, 'PARENT_ARCHIVE_BLOB'
for path, digest in r.PINS.items():
    assert sha(blob(r.SOURCE_REFS[path], path)) == digest, path
runpy.run_path('scripts/test_neumann_rectangle_directional_masks_hot_template.py', run_name='__main__')
print('ACTUAL_MASK_HOT_PACKAGE=PASS EXACT_TEMPLATE=1 REAL_PARENT_REVIEW=1 SOURCE_PINS=4 COMPILER_CHECKED=0')
print('RUNNER_SHA256=' + sha(rb))
