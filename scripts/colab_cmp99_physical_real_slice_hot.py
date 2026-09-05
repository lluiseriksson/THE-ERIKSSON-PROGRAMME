"""Bounded physical real-slice diagnostic, only after verified F5 cold PASS.

Reuses the retained cold checkout without changing its production sources.
Mathlib-only carrier repro first, then prerequisites and four draft audits.
No cold seal, regional B0 or terminal-counter claim follows from HOT PASS.
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

SOURCE = 'e833ec7e7e52ce4dbb1431777e715039ae567c23'
COLD_SOURCE = '6c49a8daeb6d6c6f60ac4a2cd2bafda67a495ff4'
REV = 'cmp99-physical-green-real-slice-hot-v1'
ROOT = Path('/content/hrpoly-cmp99-point-fibre-promoted-cold-v1')
COLD_ARCHIVE = Path(str(ROOT) + '-evidence.tar.gz')
HELPERS = Path('/content/f5-promoted-cold-launch')
LOGS = Path('/content') / (REV + '-logs')
TOOLCHAIN = Path('/content/lean-4.29.0-rc6-linux/lean-4.29.0-rc6-linux/bin')
BLOBS = {
    'tmp/SourceFlowPhysicalCarrierRepro.lean':
        '514b495a62334452fecafff32bc98f834da1746df83e5694b051078a0b8d4fd2',
    'tmp/SourceFlowPhysicalGreenRealSliceDraft.lean':
        'fea0b88dfc785bf5b896233654484a05e0ffbb6daf3ef81d82cb8e2c648cc00b',
}
HELPER_HASHES = {
    'verify_cmp99_point_fibre_promoted_cold.py':
        'f9a1c8b85731e8203d9046860005a1a0f867298ca2b33be3abf17396612f0a51',
    'verify_cmp99_full_green_residue_cold.py':
        '558295bb43e74bdae3eb6508656e7b8cde756cb393376320d0c197347396a02c',
    'full_green_owner_exact_axiom_gate.py':
        '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
}
EXPECTED = frozenset('YangMills.RG.' + name for name in (
    'cmp99SourceFlowPhysicalAmbientGreen_ofReal_draft',
    'cmp99SourceFlowPhysicalStep7bFieldEquiv_apply_site_draft',
    'cmp99SourceFlowPhysicalStep7bGreen_ofReal_draft',
    'norm_cmp99SourceFlowPhysicalStep7bGreen_ofReal_apply_draft',
))


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--cold-archive-sha256', required=True)
    args = parser.parse_args()
    cold_hash = args.cold_archive_sha256.lower()
    if LOGS.exists():
        raise RuntimeError('ALREADY_STARTED_NO_REEXECUTION')
    LOGS.mkdir()
    records, outputs, axioms = [], {}, {}
    status, error = 'FAIL', None
    os.environ['PATH'] = str(TOOLCHAIN) + os.pathsep + os.environ['PATH']

    def run(stage, command):
        if any(r['stage'] == stage for r in records):
            raise RuntimeError('DUPLICATE_STAGE=' + stage)
        log = LOGS / (stage + '.log')
        print('HOT_STAGE=' + stage + ' CMD=' + json.dumps(command), flush=True)
        started = time.perf_counter()
        with log.open('wb') as stream:
            child = subprocess.run(command, cwd=ROOT, stdout=stream,
                                   stderr=subprocess.STDOUT)
        record = dict(stage=stage, command=command, cwd=str(ROOT),
            exit=child.returncode, seconds=time.perf_counter()-started,
            log=log.name, sha256=sha(log.read_bytes()))
        records.append(record)
        temporary = LOGS / 'records.json.tmp'
        temporary.write_text(json.dumps(records, sort_keys=True) + '\n')
        temporary.replace(LOGS / 'records.json')
        raw = log.read_text(errors='replace')
        print(raw[-8000:], flush=True)
        print('HOT_STAGE_RESULT=' + json.dumps(record, sort_keys=True), flush=True)
        if child.returncode:
            raise RuntimeError('FIRST_ERROR=' + stage)
        return raw

    try:
        launch_status = json.loads((HELPERS / 'launch-final-status.json').read_text())
        if launch_status != dict(status='PASS', source=COLD_SOURCE,
                                revision='cmp99-point-fibre-promoted-cold-v1'):
            raise RuntimeError('COLD_LAUNCH_NOT_PASS')
        if sha(COLD_ARCHIVE.read_bytes()) != cold_hash:
            raise RuntimeError('COLD_ARCHIVE_HASH')
        for name, digest in HELPER_HASHES.items():
            if sha((HELPERS / name).read_bytes()) != digest:
                raise RuntimeError('HELPER_HASH=' + name)
        run('verify_cold_evidence', [sys.executable,
            str(HELPERS / 'verify_cmp99_point_fibre_promoted_cold.py'),
            '--helpers', str(HELPERS), '--archive', str(COLD_ARCHIVE),
            '--sha256', cold_hash])
        if run('retained_head', ['git', 'rev-parse', 'HEAD']).strip() != COLD_SOURCE:
            raise RuntimeError('RETAINED_HEAD')
        run('retained_clean', ['git', 'diff', '--exit-code', 'HEAD', '--',
            'YangMills', 'lean-toolchain', 'lake-manifest.json'])
        if run('mathlib_pin', ['git', '-C', '.lake/packages/mathlib',
                'rev-parse', 'HEAD']).strip() != '07642720480157414db592fa85b626dafb71355b':
            raise RuntimeError('MATHLIB_PIN')
        gate = types.ModuleType('physical_real_slice_axiom_gate')
        gate_bytes = (HELPERS / 'full_green_owner_exact_axiom_gate.py').read_bytes()
        exec(compile(gate_bytes, 'pinned_axiom_gate', 'exec'), gate.__dict__)
        gate.self_test()
        for path, digest in BLOBS.items():
            url = ('https://raw.githubusercontent.com/lluiseriksson/'
                   'THE-ERIKSSON-PROGRAMME/' + SOURCE + '/' + path)
            with urllib.request.urlopen(url, timeout=60) as response:
                blob = response.read()
            if sha(blob) != digest:
                raise RuntimeError('DRAFT_HASH=' + path)
            destination = ROOT / path
            if destination.exists():
                raise RuntimeError('DRAFT_ALREADY_EXISTS=' + path)
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(blob)
            (LOGS / destination.name).write_bytes(blob)
        manifest = LOGS / 'paths.txt'
        manifest.write_text('\n'.join(BLOBS) + '\n')
        run('text_guard', [sys.executable, 'scripts/check_lean_overlay_text.py',
            '--paths-from', str(manifest), '--require-prevalidation'])
        run('import_guard', [sys.executable, 'scripts/check_lean_import_prefix.py', *BLOBS])
        repro = 'tmp/SourceFlowPhysicalCarrierRepro.lean'
        repro_out = LOGS / 'SourceFlowPhysicalCarrierRepro.olean'
        run('mathlib_carrier_repro', ['lake', 'env', 'lean', '-o', str(repro_out), repro])
        if not repro_out.is_file():
            raise RuntimeError('REPRO_OUTPUT_MISSING')
        outputs[repro_out.name] = sha(repro_out.read_bytes())
        run('physical_prerequisites', ['lake', 'build',
            'YangMills.RG.FinitePiLpRealSliceFibreTransport',
            'YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalGreenIdentification'])
        draft_out = LOGS / 'SourceFlowPhysicalGreenRealSliceDraft.olean'
        raw = run('physical_real_slice_draft', ['lake', 'env', 'lean', '-o',
            str(draft_out), 'tmp/SourceFlowPhysicalGreenRealSliceDraft.lean'])
        axioms = gate.exact_axioms(raw, EXPECTED)
        if not draft_out.is_file():
            raise RuntimeError('DRAFT_OUTPUT_MISSING')
        outputs[draft_out.name] = sha(draft_out.read_bytes())
        run('final_clean', ['git', 'diff', '--exit-code', 'HEAD', '--',
            'YangMills', 'lean-toolchain', 'lake-manifest.json'])
        if sha(COLD_ARCHIVE.read_bytes()) != cold_hash:
            raise RuntimeError('COLD_EVIDENCE_CHANGED')
        status = 'PASS'
    except Exception as exc:
        error = repr(exc)
        print('HOT_FIRST_ERROR=' + error, flush=True)
    evidence = dict(status=status, cold_seal=False, runner_rev=REV,
        draft_source=SOURCE, retained_source=COLD_SOURCE,
        cold_archive_sha256=cold_hash, source_blobs=BLOBS, helper_hashes=HELPER_HASHES,
        records=records, compiled_output_hashes=outputs, axioms=axioms, error=error,
        files={p.name: sha(p.read_bytes()) for p in sorted(LOGS.iterdir()) if p.is_file()})
    (LOGS / 'debug-evidence.json').write_text(json.dumps(evidence, sort_keys=True) + '\n')
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
