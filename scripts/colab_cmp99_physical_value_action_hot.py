"""Bounded physical value-action diagnostic after the nine-name cold PASS.

Retain the exact checkout and warm graph. Two hash-pinned source files,
Mathlib arithmetic repro first, three new physical declarations afterward.
No change to the prior cold archive; no cold seal inferred for this draft.
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

SOURCE = '7bdc0fa1e76b3e2d3d64d1822bb30459d6697979'
BASE = 'b2d5df8ad6d600317b267bf87522a8bf472e9ea0'
REV = 'cmp99-physical-value-action-hot-v1'
PYTHON = '/usr/bin/python3'
ROOT = Path('/content/hrpoly-cmp99-physical-prefix-promoted-cold-v1')
PRIOR = Path(str(ROOT) + '-evidence.tar.gz')
HELPERS = Path('/content/physical-prefix-promoted-cold-v1-launch')
LOGS = Path('/content/' + REV + '-logs')
BLOBS = {
    "tmp/SourceFlowPhysicalValueActionRepro.lean": "cbd21a27880fe7820c2d112d6d43d9899b4e29ec1d968309e75d9298e169e6ba",
    "tmp/SourceFlowPhysicalValueActionDraft.lean": "bfa16d9e39c9ee6518c9079cb61544d86864c6c87ad480af2e4ca5783bf76555"
}
HELPER_HASHES = {
    'verify_cmp99_physical_prefix_promoted_cold.py':
        '0736f672ff3aa13464a8cd167d834d93db6175ece21abc1c48bfc8807bf869cc',
    'colab_cmp99_physical_prefix_promoted_cold.py':
        'aa21ca83496681c55276fbe3f71cba3d0f17f3ae05f931abcb3d71d2ad336681',
    'verify_cmp99_full_green_residue_cold.py':
        '558295bb43e74bdae3eb6508656e7b8cde756cb393376320d0c197347396a02c',
    'full_green_owner_exact_axiom_gate.py':
        '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
}
OUTPUTS = {
    "value_action_repro": "SourceFlowPhysicalValueActionRepro.olean",
    "value_action": "SourceFlowPhysicalValueActionDraft.olean"
}
AXIOMS = {'value_action': frozenset(["YangMills.RG.cmp99SourceFlowPhysicalRealGreen_typedKernel_draft","YangMills.RG.cmp99SourceFlowPhysicalRealGreen_ownerAction_of_budget_draft","YangMills.RG.exists_cmp99SourceFlowPhysicalRealGreen_uniformValueAction_draft"])}


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
            str(HELPERS / 'verify_cmp99_physical_prefix_promoted_cold.py'),
            '--helpers', str(HELPERS), '--archive', str(PRIOR), '--sha256', prior_hash],
        'retained_head': ['git', 'rev-parse', 'HEAD'],
        'retained_clean': clean,
        'mathlib_pin': ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'],
        'text_guard': [PYTHON, 'scripts/check_lean_overlay_text.py',
            '--paths-from', str(LOGS / 'paths.txt'), '--require-prevalidation'],
        'import_guard': [PYTHON, 'scripts/check_lean_import_prefix.py', *BLOBS],
        'value_action_repro': lean('value_action_repro'),
        'prerequisites': ['lake', 'build',
            'YangMills.RG.BalabanCMP99SourceFlowPhysicalGreenRealSlice',
            'YangMills.RG.BalabanCMP99SourceFlowPhysicalOwnerDictionary',
            'YangMills.RG.BalabanCMP99SourceFlowPhysicalPointProbe',
            'YangMills.RG.BalabanCMP99SourceFlowFullPointSourceFibreBound',
            'YangMills.RG.BalabanCMP85SourceFullGreenUniformAmplitude',
            'YangMills.RG.FinitePiLpOwnerFibreAction'],
        'value_action': lean('value_action'),
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
                        revision='cmp99-physical-prefix-promoted-cold-v1', cold_seal=True)
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
        for path, digest in BLOBS.items():
            if sha((ROOT / path).read_bytes()) != digest:
                raise RuntimeError('FINAL_SOURCE_HASH=' + path)
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
