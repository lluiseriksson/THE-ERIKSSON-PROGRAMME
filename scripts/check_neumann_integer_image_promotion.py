"""Bounded textual promotion check, not compiler evidence; no pool/network."""
from pathlib import Path
import re
import runpy
import sys

sealed = '--sealed' in sys.argv

ITEMS = [('NeumannIntegerImageCountingKernelDraft', 'NeumannIntegerImageCountingKernel', [])]

def body(text):
    text = re.sub(r'/-!.*?-/', '', text, count=1, flags=re.S)
    return '\n'.join(x for x in text.splitlines() if not x.startswith('#print axioms ')).strip()

for src, dst, renames in ITEMS:
    original = Path('tmp', src + '.lean').read_text(encoding='utf-8')
    promoted = Path('YangMills/RG', dst + '.lean').read_text(encoding='utf-8')
    assert body(original) == body(promoted), 'PROOF_OR_STATEMENT_CHANGED'
    expected = [x for x in original.splitlines() if x.startswith('#print axioms ')]
    audit = Path('YangMills/RG', dst + 'Audit.lean').read_text(encoding='utf-8')
    assert [x for x in audit.splitlines() if x.startswith('#print axioms ')] == expected
    assert len(expected) == 7
    print('EXACT_PROMOTION_TEXT=PASS names=7')

paths = Path('tmp/neumann_integer_image_promotion_paths.txt').read_text().splitlines()
for script, args in [
    ('scripts/check_lean_overlay_text.py', ['--paths-from', 'tmp/neumann_integer_image_promotion_paths.txt'] + ([] if sealed else ['--require-prevalidation'])),
    ('scripts/check_lean_import_prefix.py', paths),
]:
    sys.argv = [script, *args]
    try:
        runpy.run_path(script, run_name='__main__')
    except SystemExit as exc:
        assert exc.code in (None, 0), 'GUARD_FAILED=' + script
print('PROMOTION_STATIC_GATES=PASS COMPILER_CHECKED=0')
