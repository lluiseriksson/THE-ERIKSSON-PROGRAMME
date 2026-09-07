"""Bounded F2 diagnostic after verified full source-flow foundations PASS.

The cold archive remains immutable. Reuse its checkout only after the cold
verifier succeeds; all subsequent results are explicitly HOT, not a seal.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import time
import types
import urllib.request

SOURCE = 'b536a21679ff811ceee9bf24452fa20dd866b166'
COLD_SOURCE = '098cf3dfad1095c57bdc1d1dc5bc6b13252174d5'
ROOT = Path('/content/hrpoly-cmp99-source-flow-full-green-foundations-v1')
COLD_ARCHIVE = Path(str(ROOT) + '-evidence.tar.gz')
REV = 'cmp99-generic-full-point-source-residue-hot-v2'
LOGS = Path('/content') / (REV + '-logs')
# The pinned extractor uses an outer directory containing the asset's own
# top-level directory. Measured via /proc/<cold-lake-pid>/exe in this runtime.
TOOLCHAIN = Path('/content/lean-4.29.0-rc6-linux/lean-4.29.0-rc6-linux/bin')
BLOBS = {
    'YangMills/RG/BalabanCMP99SourceFlatFullPointSourceOwnerResidueIdentity.lean':
        'a6c552d832c83c0d2a230eb4257b57a5b175c0313c554c9de304cd9987cbd99a',
    'YangMills/RG/BalabanCMP99SourceFlatFullPointSourceOwnerResidueIdentityAudit.lean':
        '098b3a5062bec4de77f1e73953cae83964c6c6ba3832f0716a41b6e60003f343',
}
EXPECTED = {'YangMills.RG.cmp99SourceFlatFullPointSourceSolution_eq_scaledOwnerResidue'}
RECORDS = []


def sha(blob):
    return hashlib.sha256(blob).hexdigest()


def run(stage, command):
    if any(r['stage'] == stage for r in RECORDS):
        raise RuntimeError('DUPLICATE_STAGE=' + stage)
    log = LOGS / (stage + '.log')
    start = time.perf_counter()
    print('HOT_STAGE=' + stage + ' CMD=' + json.dumps(command), flush=True)
    with log.open('wb') as output:
        child = subprocess.run(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
    record = dict(stage=stage, command=command, cwd=str(ROOT), exit=child.returncode,
                  seconds=time.perf_counter() - start, log=log.name,
                  sha256=sha(log.read_bytes()))
    RECORDS.append(record)
    (LOGS / (stage + '.json')).write_text(json.dumps(record, sort_keys=True) + '\n')
    text = log.read_text(errors='replace')
    print(text[-6000:], flush=True)
    print('HOT_STAGE_RESULT=' + json.dumps(record, sort_keys=True), flush=True)
    if child.returncode != 0:
        raise RuntimeError('FIRST_ERROR=' + stage)
    return text


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--cold-archive-sha256', required=True)
    args = parser.parse_args()
    if LOGS.exists():
        raise RuntimeError('HOT_DIAGNOSTIC_ALREADY_STARTED_DO_NOT_REEXECUTE')
    if not ROOT.is_dir() or not (TOOLCHAIN / 'lake').is_file():
        raise RuntimeError('RETAINED_RUNTIME_REQUIRED')
    LOGS.mkdir()
    os.environ['PATH'] = str(TOOLCHAIN) + os.pathsep + os.environ['PATH']
    status, error = 'FAIL', None
    try:
        url = ('https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
               '3dd028d371761e0080fe9573bf750c055fdaae7a/'
               'scripts/verify_cmp99_source_flow_full_green_foundations.py')
        blob = urllib.request.urlopen(url, timeout=60).read()
        if sha(blob) != 'ee0270aae66bd98a19e22fe4294f44b35afd8d7cfe26f2f3367d51398728506c':
            raise RuntimeError('COLD_VERIFIER_HASH_MISMATCH')
        verifier = types.ModuleType('source_flow_cold_verifier_before_hot')
        exec(compile(blob, url, 'exec'), verifier.__dict__)
        old = verifier.helper(ROOT / 'scripts', 'verify_cmp99_full_green_residue_cold.py',
            '558295bb43e74bdae3eb6508656e7b8cde756cb393376320d0c197347396a02c')
        gate = verifier.helper(ROOT / 'scripts', 'full_green_owner_exact_axiom_gate.py',
            '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2')
        old.PREFIX = 'hrpoly-' + verifier.REV + '-evidence'
        report = verifier.verify(old.read_archive(COLD_ARCHIVE, args.cold_archive_sha256), gate, old)
        (LOGS / 'preceding-cold-verification.json').write_text(json.dumps(report, sort_keys=True) + '\n')
        print('PRECEDING_COLD_PASS_VERIFIED=1', flush=True)
        if run('original_head', ['git', 'rev-parse', 'HEAD']).strip() != COLD_SOURCE:
            raise RuntimeError('UNEXPECTED_RETAINED_SOURCE')
        run('original_clean', ['git', 'diff', '--exit-code', 'HEAD', '--',
                              'YangMills', 'lean-toolchain', 'lake-manifest.json'])
        run('fetch_source', ['git', 'fetch', '--no-tags', 'origin', SOURCE])
        changed = run('source_delta', ['git', 'diff', '--name-only', COLD_SOURCE, SOURCE,
                                      '--', 'YangMills']).splitlines()
        if set(changed) != set(BLOBS):
            raise RuntimeError('UNEXPECTED_MATHEMATICAL_SOURCE_DELTA')
        run('pins_delta', ['git', 'diff', '--exit-code', COLD_SOURCE, SOURCE, '--',
                           'lean-toolchain', 'lake-manifest.json'])
        run('checkout', ['git', 'checkout', '--detach', SOURCE])
        if run('head', ['git', 'rev-parse', 'HEAD']).strip() != SOURCE:
            raise RuntimeError('HOT_HEAD_MISMATCH')
        if run('mathlib', ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD']).strip() != \
                '07642720480157414db592fa85b626dafb71355b':
            raise RuntimeError('MATHLIB_PIN_MISMATCH')
        for path, expected in BLOBS.items():
            if sha((ROOT / path).read_bytes()) != expected:
                raise RuntimeError('SOURCE_BLOB_HASH_MISMATCH=' + path)
        manifest = LOGS / 'source-paths.txt'
        manifest.write_text('\n'.join(BLOBS) + '\n')
        run('text_guard', ['python3', 'scripts/check_lean_overlay_text.py',
            '--paths-from', str(manifest), '--require-prevalidation'])
        run('import_guard', ['python3', 'scripts/check_lean_import_prefix.py', *BLOBS])
        run('f2_focal', ['lake', 'build',
            'YangMills.RG.BalabanCMP99SourceFlatFullPointSourceOwnerResidueIdentity'])
        output = run('f2_audit', ['lake', 'env', 'lean',
            'YangMills/RG/BalabanCMP99SourceFlatFullPointSourceOwnerResidueIdentityAudit.lean'])
        axioms = gate.exact_axioms(output, EXPECTED)
        (LOGS / 'exact-axioms.json').write_text(json.dumps(axioms, sort_keys=True) + '\n')
        if sha(COLD_ARCHIVE.read_bytes()) != args.cold_archive_sha256.lower():
            raise RuntimeError('COLD_ARCHIVE_CHANGED')
        status = 'PASS'
    except Exception as exc:
        error = repr(exc)
        print('HOT_FIRST_ERROR=' + error, flush=True)
    data = dict(status=status, runner_rev=REV, source_sha=SOURCE,
        preceding_cold_source=COLD_SOURCE, preceding_cold_archive_sha256=args.cold_archive_sha256,
        source_blobs=BLOBS, records=RECORDS, error=error,
        project_build_cache_reused=True, cold_seal=False,
        files={p.name: sha(p.read_bytes()) for p in sorted(LOGS.iterdir()) if p.is_file()})
    (LOGS / 'debug-evidence.json').write_text(json.dumps(data, sort_keys=True) + '\n')
    archive = Path(str(LOGS) + '.tar.gz')
    with tarfile.open(archive, 'w:gz') as tar:
        tar.add(LOGS, arcname=LOGS.name)
    print('HOT_ARCHIVE=' + str(archive), flush=True)
    print('HOT_ARCHIVE_SHA256=' + sha(archive.read_bytes()), flush=True)
    print('HOT_DEBUG_STATUS=' + status + ' COLD_SEAL=0', flush=True)
    print('RUNTIME_RETAINED_FOR_EVIDENCE=1', flush=True)
    return 0 if status == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
