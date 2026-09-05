"""Bounded owner/point-probe diagnostic after verified physical retry-v2 PASS.

Retain the existing checkout and graph. Four source-pinned drafts, two
Mathlib repros first, stop on first error. HOT PASS is never a cold seal.
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

SOURCE = '6f20ead457a528c2e5df6cc5fa2318fe43dbeeda'
BASE = '59f9f522f3f731ac8a6270ac5c3ae719b1b201f6'
REV = 'cmp99-owner-point-dictionary-hot-v1'
PYTHON = '/usr/bin/python3'
ROOT = Path('/content/hrpoly-cmp99-physical-real-slice-retry-v2')
PRIOR = Path(str(ROOT) + '-evidence.tar.gz')
HELPERS = Path('/content/physical-real-slice-retry-v2-launch')
LOGS = Path('/content/' + REV + '-logs')
BLOBS = {
    'tmp/SourceFlowOwnerCastRepro.lean':
        'c0acd87b3e20bd6969f0840c77a36491a158da70072a451e0e428815fd4cc795',
    'tmp/SourceFlowPhysicalOwnerDictionaryDraft.lean':
        'c6a7d3f8d390a4f43429b6677b2c279f51120774d0d47bf6d2dfe6d6a5229f22',
    'tmp/SourceFlowPointProbeRepro.lean':
        '880f2787948d193448216da24e03576be86d68d26ca4a4226c1ea90a379d06c1',
    'tmp/SourceFlowPhysicalPointProbeDraft.lean':
        '8f6470881b61c7cfb1458d41511abe9cbc83abeb4d12c0df30d3f4acb2a4085f',
}
HELPER_HASHES = {
    'verify_cmp99_physical_real_slice_retry.py':
        '072c4a6691f0c58eddc1933390e21677e9f8f6f5ef579b3d49719133c6e20a98',
    'colab_cmp99_physical_real_slice_retry.py':
        '968ecbb45914a88114fcf341280c3e52594bf4872bed010d68fc3225d06b7846',
    'verify_cmp99_full_green_residue_cold.py':
        '558295bb43e74bdae3eb6508656e7b8cde756cb393376320d0c197347396a02c',
    'full_green_owner_exact_axiom_gate.py':
        '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
}
OUTPUTS = {
    'owner_cast_repro': 'SourceFlowOwnerCastRepro.olean',
    'point_probe_repro': 'SourceFlowPointProbeRepro.olean',
    'owner_dictionary': 'SourceFlowPhysicalOwnerDictionaryDraft.olean',
    'point_probe': 'SourceFlowPhysicalPointProbeDraft.olean',
}
AXIOMS = {
    'owner_dictionary': frozenset('YangMills.RG.' + n for n in (
        'cmp99PhysicalStep7bSiteEquiv_eq_sourceLocalization_draft',
        'cmp99PhysicalStep7b_blockSite_eq_sourceLocalizationOwner_draft',
        'card_cmp99SourceLocalizationOwner_fibre_draft')),
    'point_probe': frozenset('YangMills.RG.' + n for n in (
        'cmp99ComplexOuter_singleFinitePiLp_eq_pointSource_draft',
        'cmp99PhysicalStep7b_complexSingle_eq_pointSource_draft')),
}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def commands(prior_hash):
    clean = ['git', 'diff', '--exit-code', 'HEAD', '--',
             'YangMills', 'lean-toolchain', 'lake-manifest.json']
    def lean(stage):
        return ['lake', 'env', 'lean', '-o', str(LOGS / OUTPUTS[stage]),
                'tmp/' + OUTPUTS[stage].replace('.olean', '.lean')]
    return {
        'verify_prior': [PYTHON,
            str(HELPERS / 'verify_cmp99_physical_real_slice_retry.py'),
            '--helpers', str(HELPERS), '--archive', str(PRIOR), '--sha256', prior_hash],
        'retained_head': ['git', 'rev-parse', 'HEAD'],
        'retained_clean': clean,
        'mathlib_pin': ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'],
        'text_guard': [PYTHON, 'scripts/check_lean_overlay_text.py',
            '--paths-from', str(LOGS / 'paths.txt'), '--require-prevalidation'],
        'import_guard': [PYTHON, 'scripts/check_lean_import_prefix.py', *BLOBS],
        'owner_cast_repro': lean('owner_cast_repro'),
        'point_probe_repro': lean('point_probe_repro'),
        'prerequisites': ['lake', 'build',
            'YangMills.RG.BalabanCMP99Eq389SourceLocalizationOwner',
            'YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bCarrier',
            'YangMills.RG.FinitePiLpRealSliceFibreTransport',
            'YangMills.RG.BalabanCMP99FlatComplexFibrePointSourceFourierReconstruction'],
        'owner_dictionary': lean('owner_dictionary'),
        'point_probe': lean('point_probe'),
        'final_clean': clean,
    }


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--prior-archive-sha256', required=True)
    args = p.parse_args()
    prior_hash = args.prior_archive_sha256.lower()
    if LOGS.exists():
        raise RuntimeError('ALREADY_STARTED_NO_REEXECUTION')
    LOGS.mkdir()
    toolchain = '/content/lean-4.29.0-rc6-linux/lean-4.29.0-rc6-linux/bin'
    os.environ['PATH'] = toolchain + os.pathsep + os.environ['PATH']
    records, outputs, axioms = [], {}, {}
    status, error = 'FAIL', None

    def run(stage, command):
        print('STAGE=' + stage, flush=True)
        start = time.perf_counter()
        log = LOGS / (stage + '.log')
        with log.open('xb') as out:
            child = subprocess.run(command, cwd=ROOT, stdout=out, stderr=subprocess.STDOUT)
        r = dict(stage=stage, command=command, cwd=str(ROOT), exit=child.returncode,
                 seconds=time.perf_counter()-start, log=log.name, sha256=sha(log.read_bytes()))
        records.append(r)
        temp = LOGS / 'records.json.tmp'
        temp.write_text(json.dumps(records, sort_keys=True)+'\n')
        temp.replace(LOGS / 'records.json')
        print(json.dumps(r, sort_keys=True), flush=True)
        if child.returncode:
            print(log.read_text(errors='replace')[-8000:], flush=True)
            raise RuntimeError('FIRST_ERROR=' + stage)
        return log.read_text(errors='replace')

    try:
        expected = dict(status='PASS', source=BASE,
                        revision='cmp99-physical-real-slice-retry-v2', cold_seal=False)
        prior_status = (HELPERS / 'launch-final-status.json').read_bytes()
        (LOGS / 'prior-launch-status.json').write_bytes(prior_status)
        if json.loads(prior_status) != expected:
            raise RuntimeError('PRIOR_LAUNCH_NOT_PASS')
        if sha(PRIOR.read_bytes()) != prior_hash:
            raise RuntimeError('PRIOR_ARCHIVE_HASH')
        for name, digest in HELPER_HASHES.items():
            if sha((HELPERS / name).read_bytes()) != digest:
                raise RuntimeError('HELPER_HASH=' + name)
        gate = types.ModuleType('owner_point_pinned_axiom_gate')
        blob = (HELPERS / 'full_green_owner_exact_axiom_gate.py').read_bytes()
        exec(compile(blob, 'pinned_axiom_gate', 'exec'), gate.__dict__)
        gate.self_test()
        queue = commands(prior_hash)
        for stage in ('verify_prior', 'retained_head', 'retained_clean', 'mathlib_pin'):
            raw = run(stage, queue[stage])
            if stage == 'retained_head' and raw.strip() != BASE:
                raise RuntimeError('RETAINED_HEAD')
            if stage == 'mathlib_pin' and raw.strip() != '07642720480157414db592fa85b626dafb71355b':
                raise RuntimeError('MATHLIB_PIN')
        for path, digest in BLOBS.items():
            url = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/' + SOURCE + '/' + path
            with urllib.request.urlopen(url, timeout=60) as response:
                blob = response.read()
            if sha(blob) != digest:
                raise RuntimeError('SOURCE_HASH=' + path)
            destination = ROOT / path
            if destination.exists() and destination.read_bytes() != blob:
                raise RuntimeError('EXISTING_DRAFT_DIFFERS=' + path)
            if not destination.exists():
                destination.write_bytes(blob)
            (LOGS / destination.name).write_bytes(blob)
        (LOGS / 'paths.txt').write_text('\n'.join(BLOBS)+'\n')
        for stage in list(queue)[4:]:
            raw = run(stage, queue[stage])
            if stage in OUTPUTS:
                path = LOGS / OUTPUTS[stage]
                if not path.is_file():
                    raise RuntimeError('OUTPUT_MISSING=' + stage)
                outputs[path.name] = sha(path.read_bytes())
            if stage in AXIOMS:
                axioms[stage] = gate.exact_axioms(raw, AXIOMS[stage])
        if sha(PRIOR.read_bytes()) != prior_hash:
            raise RuntimeError('PRIOR_EVIDENCE_CHANGED')
        status = 'PASS'
    except Exception as exc:
        error = repr(exc)
        print('FIRST_ERROR=' + error, flush=True)
    present = {n: sha((LOGS/n).read_bytes()) for n in OUTPUTS.values() if (LOGS/n).is_file()}
    report = dict(status=status, cold_seal=False, source=SOURCE, retained_source=BASE,
        revision=REV, prior_archive_sha256=prior_hash, source_blobs=BLOBS,
        helper_hashes=HELPER_HASHES, records=records, successful_outputs=outputs,
        present_outputs=present, axioms=axioms, error=error,
        files={p.name: sha(p.read_bytes()) for p in sorted(LOGS.iterdir()) if p.is_file()})
    (LOGS / 'evidence.json').write_text(json.dumps(report, sort_keys=True)+'\n')
    archive = Path(str(LOGS)+'.tar.gz')
    with tarfile.open(archive, 'w:gz') as tar:
        tar.add(LOGS, arcname=LOGS.name)
    print('EVIDENCE_ARCHIVE='+str(archive), flush=True)
    print('EVIDENCE_SHA256='+sha(archive.read_bytes()), flush=True)
    print('FINAL_STATUS='+status+' COLD_SEAL=0 RUNTIME_RETAINED=1', flush=True)
    return 0 if status == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
