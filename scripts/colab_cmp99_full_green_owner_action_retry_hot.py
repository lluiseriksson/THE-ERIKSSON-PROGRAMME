"""F5 v3: beta-only repro, then the one failed owner-action draft.

Retains and verifies the v2 prefix without repeating it. HOT diagnostic,
not a cold seal; production checkout and the original cold archive unchanged.
"""
from __future__ import annotations
import json
import os
from pathlib import Path
import tarfile

# This runner's immutable helper is the already used F5 v2 implementation.
HELPER_SOURCE = 'c8e1bbacd4447034c3ce124d455a4e2a74b1b450'
HELPER_SHA = '6fbcb74de1c5ab4e4699af50bcb48300de42a0c572c823216034ac0ec1d87c97'
SOURCE = 'cee1f6d36ea8d81c5f301860f0a349b14efac47d'
REV = 'cmp99-full-green-owner-action-hot-v3'
ROOT = Path('/content/hrpoly-cmp85-uniform-full-green-promoted-cold-v1')
LOGS = Path('/content') / (REV + '-logs')
PRIOR = Path('/content/cmp99-full-green-fibre-prefix-hot-v2-logs.tar.gz')
PRIOR_SHA = '966eaa348af6724008e8b3710d9b3836fa203f967fbb50a23d206ba53231b876'
COLD_SHA = '763b8dd2c621de31c9c2f828266226f394f99e058251f9356a30cb8a97e6488a'
OLD_OWNER_SHA = 'd9b3502ebbb54d3520bc97af2506573c57d986a6ee5e3ea5d2bca146f7395b79'
BLOBS = {
    'tmp/FullGreenOwnerBetaRepro.lean':
        'bee7674b532a2add96270f2af68f272a187d8e86a0904fb3a68b88bfb2577ce7',
    'tmp/FullGreenOwnerFibreActionDraft.lean':
        '4d99b20317e44807bb97538f6e393a6d2c2e5fa9f1ab34de88a28c635861bff5',
}

def main():
    import hashlib
    import types
    import urllib.request
    def sha(b):
        return hashlib.sha256(b).hexdigest()
    if LOGS.exists():
        raise RuntimeError('V3_ALREADY_STARTED_NO_REEXECUTION')
    url = ('https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
           + HELPER_SOURCE + '/scripts/colab_cmp99_full_green_fibre_prefix_hot.py')
    helper_bytes = urllib.request.urlopen(url, timeout=60).read()
    if sha(helper_bytes) != HELPER_SHA:
        raise RuntimeError('HELPER_HASH_MISMATCH')
    h = types.ModuleType('f5_v2_helper')
    exec(compile(helper_bytes, 'f5_v2_helper', 'exec'), h.__dict__)
    base = h.module(h.fetched('bab82db79c118ef64259bc50627170f11c2e187e',
        'scripts/colab_cmp99_generic_full_point_source_residue_hot.py',
        '36032ac8bb14bbf4a3a991c4ac394d0620aadcf1dd6f38e0749672f3e658c8a2'),
        'f5_v3_recording_base')
    LOGS.mkdir()
    base.ROOT, base.LOGS, base.RECORDS = ROOT, LOGS, []
    os.environ['PATH'] = str(base.TOOLCHAIN) + os.pathsep + os.environ['PATH']
    status, error = 'FAIL', None
    compiled = {}
    try:
        if sha(PRIOR.read_bytes()) != PRIOR_SHA:
            raise RuntimeError('PRIOR_V2_ARCHIVE_HASH')
        with tarfile.open(PRIOR) as tar:
            files = {}
            for m in tar.getmembers():
                if m.isdir():
                    continue
                if not m.isfile() or m.size > 8000000:
                    raise RuntimeError('PRIOR_ARCHIVE_MEMBER')
                prefix = 'cmp99-full-green-fibre-prefix-hot-v2-logs/'
                if not m.name.startswith(prefix):
                    raise RuntimeError('PRIOR_ARCHIVE_PREFIX')
                name = m.name[len(prefix):]
                if '/' in name or name in files:
                    raise RuntimeError('PRIOR_ARCHIVE_DUPLICATE_OR_NESTING')
                files[name] = tar.extractfile(m).read()
        prior = json.loads(files['debug-evidence.json'])
        if (prior['status'] != 'FAIL' or prior['cold_seal'] or
                prior['draft_source'] != 'a289ee24dc41c25f2480c408de45b3105b09ce71'):
            raise RuntimeError('PRIOR_STATUS_OR_SOURCE')
        if set(files) != set(prior['files']) | {'debug-evidence.json'}:
            raise RuntimeError('PRIOR_EXACT_FILE_SET')
        for name, digest in prior['files'].items():
            if sha(files[name]) != digest:
                raise RuntimeError('PRIOR_FILE_HASH=' + name)
        expected = ['retained_head', 'retained_clean', 'mathlib_pin', 'text_guard',
                    'import_guard', 'mathlib_only_repro', 'f5_prerequisites',
                    'real_slice_draft', 'point_fibre_draft', 'owner_action_draft']
        if [r['stage'] for r in prior['records']] != expected:
            raise RuntimeError('PRIOR_EXACT_STAGE_SET')
        if [r['exit'] for r in prior['records']] != [0] * 9 + [1]:
            raise RuntimeError('PRIOR_EXACT_EXIT_VECTOR')
        for r in prior['records']:
            if sha(files[r['log']]) != r['sha256']:
                raise RuntimeError('PRIOR_RAW_LOG_HASH')
        gate = h.module(h.fetched(HELPER_SOURCE,
            'scripts/full_green_owner_exact_axiom_gate.py', h.GATE_HASH), 'f5_v3_gate')
        for stage in ['real_slice_draft', 'point_fibre_draft']:
            gate.exact_axioms(files[stage + '.log'].decode(), h.AUDITS[stage])
        (LOGS / 'prior-prefix-verification.json').write_text(json.dumps(
            dict(status='PASS', prior_archive_sha256=PRIOR_SHA,
                 reused_stages=expected[:-1], exact_public_audits=6), sort_keys=True) + '\n')
        if base.run('retained_head', ['git', 'rev-parse', 'HEAD']).strip() != h.COLD_SOURCE:
            raise RuntimeError('RETAINED_HEAD')
        base.run('retained_clean', ['git', 'diff', '--exit-code', 'HEAD', '--',
            'YangMills', 'lean-toolchain', 'lake-manifest.json'])
        if base.run('mathlib_pin', ['git', '-C', '.lake/packages/mathlib',
            'rev-parse', 'HEAD']).strip() != h.MATHLIB:
            raise RuntimeError('MATHLIB_PIN')
        if sha(h.COLD_ARCHIVE.read_bytes()) != COLD_SHA:
            raise RuntimeError('COLD_ARCHIVE_HASH')
        for path, digest in BLOBS.items():
            b = h.fetched(SOURCE, path, digest)
            dest = ROOT / path
            if dest.exists() and dest.read_bytes() != b:
                previous = dest.read_bytes()
                if path != 'tmp/FullGreenOwnerFibreActionDraft.lean' or sha(previous) != OLD_OWNER_SHA:
                    raise RuntimeError('UNEXPECTED_DRAFT_REPLACEMENT')
                (LOGS / 'FullGreenOwnerFibreAction.previous.lean').write_bytes(previous)
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(b)
            (LOGS / dest.name).write_bytes(b)
        manifest = LOGS / 'paths.txt'
        manifest.write_text('\n'.join(BLOBS) + '\n')
        base.run('text_guard', ['python3', 'scripts/check_lean_overlay_text.py',
            '--paths-from', str(manifest), '--require-prevalidation'])
        base.run('import_guard', ['python3', 'scripts/check_lean_import_prefix.py', *BLOBS])
        for stage, path in [('mathlib_beta_repro', 'tmp/FullGreenOwnerBetaRepro.lean'),
                            ('owner_action_draft', 'tmp/FullGreenOwnerFibreActionDraft.lean')]:
            out = LOGS / Path(path).with_suffix('.olean').name
            raw = base.run(stage, ['lake', 'env', 'lean', '-o', str(out), path])
            if stage == 'owner_action_draft':
                axioms = gate.exact_axioms(raw, h.AUDITS[stage])
                (LOGS / 'owner_action-axioms.json').write_text(json.dumps(axioms, sort_keys=True) + '\n')
            if not out.is_file():
                raise RuntimeError('OUTPUT_MISSING=' + stage)
            compiled[out.name] = sha(out.read_bytes())
        base.run('final_clean', ['git', 'diff', '--exit-code', 'HEAD', '--',
            'YangMills', 'lean-toolchain', 'lake-manifest.json'])
        if sha(h.COLD_ARCHIVE.read_bytes()) != COLD_SHA or sha(PRIOR.read_bytes()) != PRIOR_SHA:
            raise RuntimeError('PREVIOUS_EVIDENCE_CHANGED')
        status = 'PASS'
    except Exception as exc:
        error = repr(exc)
        print('HOT_FIRST_ERROR=' + error, flush=True)
    evidence = dict(status=status, runner_rev=REV, draft_source=SOURCE,
        retained_source=h.COLD_SOURCE, source_blobs=BLOBS, records=base.RECORDS,
        cold_seal=False, prior_archive_sha256=PRIOR_SHA, cold_archive_sha256=COLD_SHA,
        error=error, compiled_output_hashes=compiled,
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
