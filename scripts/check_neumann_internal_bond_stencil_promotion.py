"""Exact HOT-source promotion and textual gates; no compiler evidence."""
from pathlib import Path
import re
import runpy
import subprocess
import sys

ITEMS = [('c0174bbcb8f9b2b791cdb2c546206b468fd4e3cf', 'NeumannInternalBondStencil', 4)]

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
manifest = 'tmp/neumann_internal_bond_stencil_promotion_paths.txt'
paths = Path(manifest).read_text().splitlines()
for script, args in [
    ('scripts/check_lean_overlay_text.py', ['--paths-from', manifest] + ([] if sealed else ['--require-prevalidation'])),
    ('scripts/check_lean_import_prefix.py', paths),
]:
    sys.argv = [script, *args]
    try:
        runpy.run_path(script, run_name='__main__')
    except SystemExit as e:
        assert e.code in (None, 0)
print('INTERNAL_BOND_STENCIL_PROMOTION_STATIC=PASS COMPILER_CHECKED=0')
