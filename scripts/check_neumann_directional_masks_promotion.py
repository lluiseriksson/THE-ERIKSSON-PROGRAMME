"""Exact HOT-body promotion and shipped-file text/import gates; no compiler."""
from pathlib import Path
import re
import runpy
import subprocess
import sys

SOURCE = 'adfef2b5b883a839e24b03ceedd118b32428dace'
NAME = 'NeumannRectangleDirectionalMasks'
sealed = '--sealed' in sys.argv
original = subprocess.check_output(['git', 'cat-file', 'blob',
    SOURCE + ':tmp/' + NAME + 'Draft.lean'], timeout=5).decode()
promoted = Path('YangMills/RG', NAME + '.lean').read_text(encoding='utf-8')
def body(s):
    s = re.sub(r'/-!.*?-/', '', s, count=1, flags=re.S)
    return '\n'.join(l for l in s.splitlines() if not l.startswith('#print axioms ')).strip()
assert body(original) == body(promoted), 'STATEMENT_OR_PROOF_CHANGED'
expected = [l.replace('#print axioms ', '#print axioms YangMills.RG.')
    for l in original.splitlines() if l.startswith('#print axioms ')]
audit = Path('YangMills/RG', NAME + 'Audit.lean').read_text(encoding='utf-8')
assert len(expected) == 4
assert [l for l in audit.splitlines() if l.startswith('#print axioms ')] == expected
manifest = 'tmp/neumann_directional_masks_promotion_paths.txt'
paths = [l for l in Path(manifest).read_text().splitlines() if l.strip()]
assert paths == ['YangMills/RG/' + NAME + '.lean', 'YangMills/RG/' + NAME + 'Audit.lean']
for script, args in [
    ('scripts/check_lean_overlay_text.py', ['--paths-from', manifest] + ([] if sealed else ['--require-prevalidation'])),
    ('scripts/check_lean_import_prefix.py', paths),
]:
    sys.argv = [script, *args]
    try:
        runpy.run_path(script, run_name='__main__')
    except SystemExit as e:
        assert e.code in (None, 0)
print('EXACT_MASK_HOT_BODY_PROMOTION=PASS FILES=2 NAMES=4 COMPILER_CHECKED=0')
