"""Exact HOT-source promotion and textual gates; no compiler evidence."""
from pathlib import Path
import re
import runpy
import subprocess
import sys

ITEMS = [
    ('eb2fde64ff5597e6c3fa49d3beb114633e806d37', 'NeumannGeneratedIntegerCountingKernel', 4),
    ('99d0767ec84ed79e633556653bc2fe05047c79cf', 'NeumannImageIntervalCoverage', 7),
]

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
    assert [x for x in audit.splitlines() if x.startswith('#print axioms ')] == expected
    assert len(expected) == count
    print('EXACT_HOT_BLOB_PROMOTION=PASS module=' + name + ' names=' + str(count))
manifest = 'tmp/neumann_integer_dictionary_cohort_paths.txt'
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
print('DICTIONARY_PROMOTION_STATIC=PASS COMPILER_CHECKED=0')
