"""One bounded warm diagnostic; never a cold seal or a physical B0 claim.

Run only after the F2-F3 cold archive has passed its exact verifier and been
preserved. The cold checkout and archive stay unchanged. The single draft
is fetched from its immutable Git blob, checked, then elaborated separately.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
import tarfile
import types
import urllib.request

RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
COLD_SOURCE = 'bab82db79c118ef64259bc50627170f11c2e187e'
DRAFT_SOURCE = '16e95f064febb67b29b797648a38f3cb27e8c502'
DRAFT_PATH = 'tmp/SourceFullGreenHybridAmplitudeDraft.lean'
DRAFT_HASH = '01d8599984547801cb2e11990bfe08bd5103b10f08fa209eca9a59b5133ea7c8'
ROOT = Path('/content/hrpoly-cmp99-source-flow-full-green-owner-v1')
ARCHIVE = Path(str(ROOT) + '-evidence.tar.gz')
REV = 'cmp85-full-green-hybrid-draft-hot-v1'
LOGS = Path('/content') / (REV + '-logs')
EXPECTED = {'YangMills.RG.cmp85SourceFullGreen_fullBudget_le_hybrid_draft'}


def fetch(commit, path, expected):
    url = RAW + commit + '/' + path
    with urllib.request.urlopen(url, timeout=60) as response:
        blob = response.read()
    if hashlib.sha256(blob).hexdigest() != expected:
        raise RuntimeError('TRANSPORT_HASH_MISMATCH=' + path)
    return blob, url


def module(commit, path, expected, name):
    blob, url = fetch(commit, path, expected)
    result = types.ModuleType(name)
    exec(compile(blob, url, 'exec'), result.__dict__)
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--cold-archive-sha256', required=True)
    args = parser.parse_args()
    if LOGS.exists():
        raise RuntimeError('HOT_ALREADY_STARTED_DO_NOT_REEXECUTE')
    base = module(COLD_SOURCE,
        'scripts/colab_cmp99_generic_full_point_source_residue_hot.py',
        '36032ac8bb14bbf4a3a991c4ac394d0620aadcf1dd6f38e0749672f3e658c8a2',
        'hybrid_hot_recording_base')
    if not ROOT.is_dir() or not (base.TOOLCHAIN / 'lake').is_file():
        raise RuntimeError('RETAINED_RUNTIME_REQUIRED')
    LOGS.mkdir()
    base.ROOT, base.LOGS, base.RECORDS = ROOT, LOGS, []
    os.environ['PATH'] = str(base.TOOLCHAIN) + os.pathsep + os.environ['PATH']
    status, error = 'FAIL', None
    try:
        verifier = module('dcbac7ff2f8436f7f6facd8cedff0bc0da4361f1',
            'scripts/verify_cmp99_source_flow_full_green_owner.py',
            '535c22f5da3b799510d6fefdbfac0c088fad25af35d44aa008f82ae8dbcfac45',
            'owner_cold_verifier_before_hybrid')
        old = verifier.helper(ROOT / 'scripts', 'verify_cmp99_full_green_residue_cold.py',
            '558295bb43e74bdae3eb6508656e7b8cde756cb393376320d0c197347396a02c')
        gate = verifier.helper(ROOT / 'scripts', 'full_green_owner_exact_axiom_gate.py',
            '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2')
        old.PREFIX = 'hrpoly-' + verifier.REV + '-evidence'
        report = verifier.verify(old.read_archive(ARCHIVE, args.cold_archive_sha256), gate, old)
        (LOGS / 'preceding-cold-verification.json').write_text(json.dumps(report, sort_keys=True) + '\n')
        print('PRECEDING_COLD_PASS_VERIFIED=1', flush=True)
        if base.run('head', ['git', 'rev-parse', 'HEAD']).strip() != COLD_SOURCE:
            raise RuntimeError('RETAINED_SOURCE_MISMATCH')
        base.run('clean', ['git', 'diff', '--exit-code', 'HEAD', '--',
                          'YangMills', 'lean-toolchain', 'lake-manifest.json'])
        if base.run('mathlib', ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD']).strip() != \
                '07642720480157414db592fa85b626dafb71355b':
            raise RuntimeError('MATHLIB_PIN_MISMATCH')
        blob, _ = fetch(DRAFT_SOURCE, DRAFT_PATH, DRAFT_HASH)
        draft = LOGS / 'SourceFullGreenHybridAmplitudeDraft.lean'
        draft.write_bytes(blob)
        (LOGS / 'source-paths.txt').write_text(str(draft) + '\n')
        base.run('text_guard', ['python3', 'scripts/check_lean_overlay_text.py',
            '--paths-from', str(LOGS / 'source-paths.txt'), '--require-prevalidation'])
        base.run('import_guard', ['python3', 'scripts/check_lean_import_prefix.py', str(draft)])
        base.run('materialize_sealed_imports', ['lake', 'build',
            'YangMills.RG.BalabanCMP85SourceFullGreenScalarFoundations',
            'YangMills.RG.BalabanCMP99PhysicalFullGreenOwnerResidueBound'])
        output = base.run('hybrid_draft', ['lake', 'env', 'lean', str(draft)])
        axioms = gate.exact_axioms(output, EXPECTED)
        (LOGS / 'exact-axioms.json').write_text(json.dumps(axioms, sort_keys=True) + '\n')
        if base.sha(ARCHIVE.read_bytes()) != args.cold_archive_sha256.lower():
            raise RuntimeError('COLD_ARCHIVE_CHANGED')
        status = 'PASS'
    except Exception as exc:
        error = repr(exc)
        print('HOT_FIRST_ERROR=' + error, flush=True)
    evidence = dict(status=status, runner_rev=REV, source_sha=COLD_SOURCE,
        draft_source=DRAFT_SOURCE, draft_path=DRAFT_PATH, draft_sha256=DRAFT_HASH,
        preceding_cold_archive_sha256=args.cold_archive_sha256, records=base.RECORDS,
        error=error, project_build_cache_reused=True, cold_seal=False,
        files={p.name: base.sha(p.read_bytes()) for p in sorted(LOGS.iterdir()) if p.is_file()})
    (LOGS / 'debug-evidence.json').write_text(json.dumps(evidence, sort_keys=True) + '\n')
    archive = Path(str(LOGS) + '.tar.gz')
    with tarfile.open(archive, 'w:gz') as tar:
        tar.add(LOGS, arcname=LOGS.name)
    print('HOT_ARCHIVE=' + str(archive), flush=True)
    print('HOT_ARCHIVE_SHA256=' + base.sha(archive.read_bytes()), flush=True)
    print('HOT_DEBUG_STATUS=' + status + ' COLD_SEAL=0', flush=True)
    print('RUNTIME_RETAINED_FOR_EVIDENCE=1', flush=True)
    return 0 if status == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
