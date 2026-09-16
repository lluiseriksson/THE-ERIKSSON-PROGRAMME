"""Single-process bounded textual gate; no compilation or network."""
from pathlib import Path
import runpy
import sys

p = Path('tmp/NeumannImageIntervalCoverageDraft.lean')
s = p.read_text(encoding='utf-8')
assert s.count('#print axioms YangMills.RG.') == 7
assert s.count('PRE-VALIDATION') == 1
assert 'NeumannGeneratedIntegerCountingKernel' not in s
for path in ('Mathlib/Data/Int/DivMod.lean', 'Mathlib/Tactic/Linarith.lean', 'Mathlib/Tactic/Ring.lean'):
    assert (Path('.lake/packages/mathlib') / path).is_file(), 'UNKNOWN_IMPORT=' + path
for script, args in [
    ('scripts/check_lean_overlay_text.py', ['--paths-from', 'tmp/neumann_image_interval_coverage_paths.txt', '--require-prevalidation']),
    ('scripts/check_lean_import_prefix.py', [str(p)]),
]:
    sys.argv = [script, *args]
    try:
        runpy.run_path(script, run_name='__main__')
    except SystemExit as e:
        assert e.code in (None, 0)
print('INTERVAL_COVERAGE_TEXT_OK COMPILER_CHECKED=0')
