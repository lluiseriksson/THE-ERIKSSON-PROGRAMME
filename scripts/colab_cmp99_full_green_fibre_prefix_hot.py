"""One F5 point/fibre diagnostic on the retained verified F4 runtime.

This is HOT diagnostic evidence, never a cold seal. It preserves the F4
archive, does not change checkout, and stops at the first failed child.
The Mathlib-only reproduction precedes every project-dependent elaboration.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import tarfile
import types
import urllib.request

SOURCE = 'a289ee24dc41c25f2480c408de45b3105b09ce71'
COLD_SOURCE = '5138e9bd4bc88797c91c21df5bb5c630c71600ca'
ROOT = Path('/content/hrpoly-cmp85-uniform-full-green-promoted-cold-v1')
COLD_ARCHIVE = Path(str(ROOT) + '-evidence.tar.gz')
LAUNCH = Path('/content/f4-promoted-cold-launch')
REV = 'cmp99-full-green-fibre-prefix-hot-v2'
LOGS = Path('/content') / (REV + '-logs')
RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
BLOBS = {
    'tmp/FullGreenFibreNormRepro.lean':
        '7dd63272dc90578f15e59aa0398c7811219c7ba008c8752f2d4b70d4c5354234',
    'tmp/FinitePiLpRealSliceFibreTransportDraft.lean':
        '66cd10f0573976ad5793fa35ca311cb8ea42f8dccabeabe62648389d00d3956b',
    'tmp/SourceFlowFullPointSourceFibreBoundDraft.lean':
        '856ec6f6491089306e9c38159b0743c9875eb1bfb2472f938be05af3fb21b223',
    'tmp/FullGreenOwnerFibreActionDraft.lean':
        'd9b3502ebbb54d3520bc97af2506573c57d986a6ee5e3ea5d2bca146f7395b79',
}
AUDITS = {
    'real_slice_draft': {
        'YangMills.RG.norm_cmp99SUNLieCoordComplexificationLM_draft',
        'YangMills.RG.norm_finitePiLpComplexOfReal_apply_draft',
        'YangMills.RG.finitePiLpCanonicalComplexificationOuterCLM_ofReal_draft',
        'YangMills.RG.norm_finitePiLpCanonicalComplexificationOuterCLM_ofReal_apply_draft',
    },
    'point_fibre_draft': {
        'YangMills.RG.norm_euclidean_of_common_scalar_draft',
        'YangMills.RG.norm_cmp99SourceFlowFullPointSourceGreen_fibre_le_owner_draft',
    },
    'owner_action_draft': {'YangMills.RG.fullGreenOwnerFibreActionDraft'},
}
QUEUE = [
    ('real_slice_draft', 'tmp/FinitePiLpRealSliceFibreTransportDraft.lean'),
    ('point_fibre_draft', 'tmp/SourceFlowFullPointSourceFibreBoundDraft.lean'),
    ('owner_action_draft', 'tmp/FullGreenOwnerFibreActionDraft.lean'),
]
VERIFIER_HASH = 'f408dc8cb99fa1131f4b444f519c35a741dafc643f34e3881f4c49737e153da9'
GATE_HASH = '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'
MATHLIB = '07642720480157414db592fa85b626dafb71355b'
PREVIOUS_REPRO_HASH = 'fd7882b6d46d20c1ee2ca67206fed6a2df7149e4c705339e1a587ed78fb91da9'
PREVIOUS_HOT_ARCHIVE = Path('/content/cmp99-full-green-fibre-prefix-hot-v1-logs.tar.gz')
PREVIOUS_HOT_HASH = '180ee030bd3dffda8dc964582e05bd1c4fa7b81b8cd7836b86657d636f5011ec'

def sha(blob):
    return hashlib.sha256(blob).hexdigest()

def module(blob, name):
    result = types.ModuleType(name)
    exec(compile(blob, name, 'exec'), result.__dict__)
    return result

def fetched(commit, path, digest):
    with urllib.request.urlopen(RAW + commit + '/' + path, timeout=60) as r:
        blob = r.read()
    if sha(blob) != digest:
        raise RuntimeError('TRANSPORT_HASH_MISMATCH=' + path)
    return blob

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--cold-archive-sha256', required=True)
    args = parser.parse_args()
    if (len(QUEUE) != 3 or len(AUDITS) != 3 or len(BLOBS) != 4 or
            {s for s, _ in QUEUE} != set(AUDITS) or
            {p for _, p in QUEUE} != set(BLOBS) - {'tmp/FullGreenFibreNormRepro.lean'}):
        raise RuntimeError('FINITE_QUEUE_CONTRACT_MISMATCH')
    if LOGS.exists():
        raise RuntimeError('HOT_ALREADY_STARTED_NO_REEXECUTION')
    base = module(fetched('bab82db79c118ef64259bc50627170f11c2e187e',
        'scripts/colab_cmp99_generic_full_point_source_residue_hot.py',
        '36032ac8bb14bbf4a3a991c4ac394d0620aadcf1dd6f38e0749672f3e658c8a2'),
        'f5_recording_base')
    if not ROOT.is_dir() or not (base.TOOLCHAIN / 'lake').is_file():
        raise RuntimeError('RETAINED_COLAB_RUNTIME_REQUIRED')
    LOGS.mkdir()
    base.ROOT, base.LOGS, base.RECORDS = ROOT, LOGS, []
    os.environ['PATH'] = str(base.TOOLCHAIN) + os.pathsep + os.environ['PATH']
    status, error = 'FAIL', None
    compiled = {}
    try:
        if sha(PREVIOUS_HOT_ARCHIVE.read_bytes()) != PREVIOUS_HOT_HASH:
            raise RuntimeError('PREVIOUS_HOT_EVIDENCE_HASH')
        launch_records = json.loads((LAUNCH / 'launch-records.json').read_text())
        if [r['stage'] for r in launch_records] != [
                'verifier_self_test', 'cold_graph', 'archive_verifier']:
            raise RuntimeError('COLD_LAUNCH_NOT_FINISHED')
        if any(r['exit'] != 0 for r in launch_records):
            raise RuntimeError('COLD_LAUNCH_CHILD_FAILURE')
        for record in launch_records:
            if sha((LAUNCH / (record['stage'] + '.log')).read_bytes()) != record['log_sha256']:
                raise RuntimeError('COLD_LAUNCH_LOG_HASH')
        if Path('/content/f4-promoted-cold-exit.txt').read_text().strip() != '0':
            raise RuntimeError('COLD_LAUNCH_EXIT_NOT_ZERO')
        vb = (LAUNCH / 'verify_cmp85_uniform_full_green_promoted_cold.py').read_bytes()
        if sha(vb) != VERIFIER_HASH:
            raise RuntimeError('COLD_VERIFIER_HASH')
        verifier = module(vb, 'f4_verifier_before_f5')
        old = verifier.helper(LAUNCH, 'verify_cmp99_full_green_residue_cold.py',
            '558295bb43e74bdae3eb6508656e7b8cde756cb393376320d0c197347396a02c')
        gate = verifier.helper(LAUNCH, 'full_green_owner_exact_axiom_gate.py', GATE_HASH)
        old.PREFIX = 'hrpoly-' + verifier.REV + '-evidence'
        report = verifier.verify(old.read_archive(COLD_ARCHIVE,
            args.cold_archive_sha256), gate, old)
        (LOGS / 'preceding-cold-verification.json').write_text(
            json.dumps(report, sort_keys=True) + '\n')
        if base.run('retained_head', ['git', 'rev-parse', 'HEAD']).strip() != COLD_SOURCE:
            raise RuntimeError('RETAINED_HEAD_MISMATCH')
        base.run('retained_clean', ['git', 'diff', '--exit-code', 'HEAD', '--',
            'YangMills', 'lean-toolchain', 'lake-manifest.json'])
        if base.run('mathlib_pin', ['git', '-C', '.lake/packages/mathlib',
                'rev-parse', 'HEAD']).strip() != MATHLIB:
            raise RuntimeError('MATHLIB_PIN_MISMATCH')
        # Fetch immutable text. Only the failed tmp repro may change, and
        # only from its recorded v1 bytes; preserve those bytes in this log.
        # No production source, checkout or project-build restoration changes.
        for path, digest in BLOBS.items():
            blob = fetched(SOURCE, path, digest)
            dest = ROOT / path
            if dest.exists() and dest.read_bytes() != blob:
                previous = dest.read_bytes()
                if (path != 'tmp/FullGreenFibreNormRepro.lean' or
                        sha(previous) != PREVIOUS_REPRO_HASH):
                    raise RuntimeError('EXISTING_DRAFT_DIFFERS=' + path)
                if previous.replace(b'WithLp.toLp_apply', b'PiLp.toLp_apply') != blob:
                    raise RuntimeError('REPRO_REPAIR_NOT_EXACT')
                (LOGS / 'FullGreenFibreNormRepro.previous.lean').write_bytes(previous)
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(blob)
            (LOGS / dest.name).write_bytes(blob)
        manifest = LOGS / 'paths.txt'
        manifest.write_text('\n'.join(BLOBS) + '\n')
        base.run('text_guard', ['python3', 'scripts/check_lean_overlay_text.py',
            '--paths-from', str(manifest), '--require-prevalidation'])
        base.run('import_guard', ['python3', 'scripts/check_lean_import_prefix.py', *BLOBS])
        path = 'tmp/FullGreenFibreNormRepro.lean'
        out = LOGS / 'FullGreenFibreNormRepro.olean'
        base.run('mathlib_only_repro', ['lake', 'env', 'lean', '-o', str(out), path])
        if not out.is_file():
            raise RuntimeError('REPRO_OUTPUT_MISSING')
        compiled[out.name] = sha(out.read_bytes())
        base.run('f5_prerequisites', ['lake', 'build',
            'YangMills.RG.BalabanCMP99SourceFlowFullPointSourceOwnerBound',
            'YangMills.RG.FinitePiLpBlockLocalizedSup'])
        for stage, path in QUEUE:
            out = LOGS / Path(path).with_suffix('.olean').name
            text = base.run(stage, ['lake', 'env', 'lean', '-o', str(out), path])
            axioms = gate.exact_axioms(text, AUDITS[stage])
            (LOGS / (stage + '-axioms.json')).write_text(
                json.dumps(axioms, sort_keys=True) + '\n')
            if not out.is_file():
                raise RuntimeError('MISSING_COMPILED_OUTPUT=' + path)
            compiled[out.name] = sha(out.read_bytes())
        base.run('final_clean', ['git', 'diff', '--exit-code', 'HEAD', '--',
            'YangMills', 'lean-toolchain', 'lake-manifest.json'])
        if sha(COLD_ARCHIVE.read_bytes()) != args.cold_archive_sha256.lower():
            raise RuntimeError('COLD_ARCHIVE_CHANGED')
        if sha(PREVIOUS_HOT_ARCHIVE.read_bytes()) != PREVIOUS_HOT_HASH:
            raise RuntimeError('PREVIOUS_HOT_ARCHIVE_CHANGED')
        status = 'PASS'
    except Exception as exc:
        error = repr(exc)
        print('HOT_FIRST_ERROR=' + error, flush=True)
    evidence = dict(status=status, runner_rev=REV, retained_source=COLD_SOURCE,
        draft_source=SOURCE, source_blobs=BLOBS, records=base.RECORDS, error=error,
        previous_archive_sha256=args.cold_archive_sha256,
        project_build_cache_reused=True, cold_seal=False,
        compiled_output_hashes=compiled,
        audit_expected={s:sorted(v) for s,v in AUDITS.items()},
        files={p.name:sha(p.read_bytes()) for p in sorted(LOGS.iterdir()) if p.is_file()})
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
