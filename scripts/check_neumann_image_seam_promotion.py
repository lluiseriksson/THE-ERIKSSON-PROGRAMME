"""Read-only, bounded six-file promotion equivalence gate; never invokes Lean."""
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'efdbce22459e76d05a728f912a786d7f571dad3d'
MAPPING = {
    'NeumannBoundaryOrbitPermutationRepro': 'NeumannBoundaryOrbitPermutation',
    'NeumannBoundaryImagePermutationDraft': 'NeumannBoundaryImagePermutation',
    'NeumannBoundaryImageSeriesReindexDraft': 'NeumannBoundaryImageSeriesReindex',
    'NeumannPhysicalBoundaryTransferDraft': 'NeumannPhysicalBoundaryTransfer',
    'NeumannPhysicalImageSeamDraft': 'NeumannPhysicalImageSeam',
}

def main():
    records, audits = [], []
    for old, new in MAPPING.items():
        original = subprocess.run(['git', 'cat-file', 'blob', f'{SOURCE}:tmp/{old}.lean'],
            cwd=ROOT, check=True, capture_output=True, timeout=5).stdout
        text = original.decode('utf-8')
        audits.extend(line for line in text.splitlines() if line.startswith('#print axioms '))
        expected = '\n'.join(line for line in text.splitlines()
            if not line.startswith('#print axioms ')).rstrip() + '\n'
        for before, after in MAPPING.items():
            expected = expected.replace('import ' + before + '\n',
                'import YangMills.RG.' + after + '\n')
        expected = expected.replace(
            'Source present; .olean not materialized; result not compiler-verified.',
            'Promoted source present; its .olean is not materialized and this production\n'
            'module is not compiler-verified. Draft HOT evidence does not constitute a cold seal.')
        path = ROOT / 'YangMills' / 'RG' / (new + '.lean')
        actual = path.read_text(encoding='utf-8')
        # Only terminal blank lines are immaterial; all proof tokens and internal
        # whitespace must otherwise match after the declared import/header edits.
        assert actual.rstrip('\n') == expected.rstrip('\n'), f'PROMOTION_DELTA: {new}'
        records.append({'draft': old, 'production': new,
            'draft_blob_sha256': hashlib.sha256(original).hexdigest(),
            'production_lf_sha256': hashlib.sha256(actual.encode()).hexdigest()})
    audit = (ROOT / 'YangMills/RG/NeumannPhysicalImageSeamAudit.lean').read_text(encoding='utf-8')
    seen = [line for line in audit.splitlines() if line.startswith('#print axioms ')]
    assert seen == audits and len(set(audits)) == 11, 'AUDIT_COVERAGE'
    assert 'PRE-VALIDATION' in audit, 'AUDIT_MARK'
    print(json.dumps({'status': 'STATIC_PROMOTION_EQUIVALENCE_PASS',
        'source': SOURCE, 'records': records, 'audit_names': audits,
        'compiler_verified': False, 'cold_seal': False}, indent=2))

if __name__ == '__main__':
    main()
