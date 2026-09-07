"""Exact HOT-source promotion and textual gates; no compiler evidence."""
from pathlib import Path
import re
import runpy
import subprocess
import sys

ITEMS = [["baf5fa136663fe71a9cf07dacd4e365b0026942e","NeumannRectangleWrapProbe",1],["69a5308c8e5635b95b59c6d5c88d4b5b789f851c","NeumannFlatInternalBondAction",2]]

def body(t):
    t = re.sub(r'/-!.*?-/', '', t, count=1, flags=re.S)
    return '\n'.join(x for x in t.splitlines() if not x.startswith('#print axioms ')).strip()

sealed = '--sealed' in sys.argv
for commit, name, count in ITEMS:
    b = subprocess.check_output(['git', 'cat-file', 'blob', commit + ':tmp/' + name + 'Draft.lean'], timeout=5)
    original = b.decode()
    promoted = Path('YangMills/RG', name + '.lean').read_text(encoding='utf-8')
    assert body(original) == body(promoted), 'PROOF_OR_STATEMENT_CHANGED=' + name
    expected = [x for x in original.splitlines() if x.startswith('#print axioms ')]
    audit = Path('YangMills/RG', name + 'Audit.lean').read_text(encoding='utf-8')
    assert [x for x in audit.splitlines() if x.startswith('#print axioms ')] == [x.replace('#print axioms ', '#print axioms YangMills.RG.') for x in expected]
    assert len(expected) == count
    print('EXACT_HOT_BLOB_PROMOTION=PASS module=' + name + ' names=' + str(count))
manifest = 'tmp/neumann_wrap_flat_promotion_paths.txt'
paths = [line for line in Path(manifest).read_text().splitlines() if line.strip()]
for script, args in [
    ('scripts/check_lean_overlay_text.py', ['--paths-from', manifest] + ([] if sealed else ['--require-prevalidation'])),
    ('scripts/check_lean_import_prefix.py', paths),
]:
    sys.argv = [script, *args]
    try:
        runpy.run_path(script, run_name='__main__')
    except SystemExit as e:
        assert e.code in (None, 0)
print('WRAP_FLAT_PROMOTION_STATIC=PASS COMPILER_CHECKED=0')
