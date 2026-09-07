"""Bounded textual promotion check, not compiler evidence; no pool/network."""
from pathlib import Path
import re
import runpy
import sys

sealed = '--sealed' in sys.argv

ITEMS = [
    ('NeumannGeneratedCountingMassReflectionDraft', 'NeumannGeneratedCountingMassReflection', [
        ('neumannGeneratedFullSiteReflectionDraft', 'neumannGeneratedFullSiteReflection'),
        ('neumannGeneratedTerminalOwner_reflection_draft', 'neumannGeneratedTerminalOwner_reflection'),
        ('neumannGeneratedFullCountingMass_reflection_draft', 'neumannGeneratedFullCountingMass_reflection')]),
    ('NeumannRetainedCountingMassDictionaryDraft', 'NeumannRetainedCountingMassDictionary', [
        ('neumannFlatGeneratedCountingMass_eq_explicit_draft', 'neumannFlatGeneratedCountingMass_eq_explicit'),
        ('neumannFlatRetainedTerminalCountingMass_eq_explicit_draft', 'neumannFlatRetainedTerminalCountingMass_eq_explicit')]),
]

def body(text):
    text = re.sub(r'/-!.*?-/', '', text, count=1, flags=re.S)
    return '\n'.join(x for x in text.splitlines() if not x.startswith('#print axioms ')).strip()

for src, dst, renames in ITEMS:
    original = Path('tmp', src + '.lean').read_text(encoding='utf-8')
    promoted = Path('YangMills/RG', dst + '.lean').read_text(encoding='utf-8')
    for old, new in renames:
        original = original.replace(old, new)
    assert body(original) == body(promoted), 'PROOF_OR_STATEMENT_CHANGED=' + dst
    expected = [x for x in original.splitlines() if x.startswith('#print axioms ')]
    audit = Path('YangMills/RG', dst + 'Audit.lean').read_text(encoding='utf-8')
    actual = [x for x in audit.splitlines() if x.startswith('#print axioms ')]
    assert actual == expected, 'AUDIT_NAMES=' + dst
    print('EXACT_PROMOTION_TEXT=PASS ' + dst)

paths = Path('tmp/neumann_counting_promotion_paths.txt').read_text().splitlines()
if sealed:
    for path in paths:
        text = Path(path).read_text(encoding='utf-8')
        assert 'PRE-VALIDATION:' not in text and 'ledger1130' in text, 'SEAL_HEADER=' + path
for script, args in [
    ('scripts/check_lean_overlay_text.py', ['--paths-from', 'tmp/neumann_counting_promotion_paths.txt'] +
        ([] if sealed else ['--require-prevalidation'])),
    ('scripts/check_lean_import_prefix.py', paths),
]:
    sys.argv = [script, *args]
    try:
        runpy.run_path(script, run_name='__main__')
    except SystemExit as exc:
        assert exc.code in (None, 0), 'GUARD_FAILED=' + script
print('PROMOTION_STATIC_GATES=PASS COMPILER_CHECKED=0')
