"""Bounded textual equivalence to the cold-promotion input. Never invokes Lean."""
import hashlib
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SOURCE = '3b0576aa1329025f815ebee0edd15666d6e432bd'
def main():
    blob = subprocess.check_output(['git', 'cat-file', 'blob',
        SOURCE + ':tmp/NeumannPhysicalPeriodicTransferDraft.lean'], cwd=ROOT, timeout=5)
    assert hashlib.sha256(blob).hexdigest() == '41b7242faf89cc5881f8f0b8b9eeef61035c1b946cc2a28def826b90832ab977'
    lines = blob.decode().splitlines()
    expected = '\n'.join(l for l in lines if not l.startswith('#print axioms ')).rstrip()+'\n'
    expected = expected.replace('Source present; .olean not materialized; result not compiler-verified.',
        'Promoted source present; .olean not materialized; production not compiler-verified.\nThe prior HOT diagnostic is not a cold seal.')
    actual = (ROOT/'YangMills/RG/NeumannPhysicalPeriodicTransfer.lean').read_text(encoding='utf-8')
    assert actual == expected, 'PROOF_OR_STATEMENT_CHANGED'
    audit = (ROOT/'YangMills/RG/NeumannPhysicalPeriodicTransferAudit.lean').read_text(encoding='utf-8')
    assert [l for l in audit.splitlines() if l.startswith('#print axioms ')] == [l for l in lines if l.startswith('#print axioms ')]
    assert 'PRE-VALIDATION' in actual and 'PRE-VALIDATION' in audit
    print('PERIODIC_PROMOTION_EQUIVALENCE_PASS compiler_verified=False')
if __name__ == '__main__': main()
