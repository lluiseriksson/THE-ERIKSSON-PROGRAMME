"""One bounded F4 composition diagnostic after verified hybrid PASS.

Reuse only the retained runtime. Never a cold seal. No F5/CI stage.
The preceding archive is checked before and after; checkout stays unchanged.
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

RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
SOURCE = '5d6f85e8787ad29ab0f4f6539d9b7ff5ab29b062'
PREVIOUS_SOURCE = '9dafedaa1bfc08daa258c75a41b27672b9087bb8'
ROOT = Path('/content/hrpoly-cmp85-full-green-hybrid-repro-v2')
PREVIOUS_ARCHIVE = Path(str(ROOT) + '-evidence.tar.gz')
REV = 'cmp85-uniform-full-green-hot-v2'
LOGS = Path('/content') / (REV + '-logs')
BLOBS = {
    'tmp/SourceFullGreenHybridAmplitudeDraft.lean':
        '3df28cff61bfd539dacac6e8e3ee18f175f3535f9d93bf12f59f06a6532b3882',
    'tmp/FullGreenNormalizedBudgetRepro.lean':
        'b709e6376b505d55846acd6d255a56db06d2a817b40f671dac296a0c568a1f4f',
    'tmp/SourceFullGreenUniformAmplitudeDraft.lean':
        '7c42caaac7090a8f9f91b338788e7a86f4af55a429b9cf31be160cdd0a4d6fb0',
}
AUDITS = {
    'hybrid_import': {'YangMills.RG.cmp85SourceFullGreen_fullBudget_le_hybrid_draft'},
    'normalization_import': {'FullGreenNormalizedBudgetRepro.split',
        'FullGreenNormalizedBudgetRepro.retain_inverse_square'},
    'uniform_draft': {'YangMills.RG.' + name for name in (
        'cmp85SourceFullGreenContourFactorDraft_pos',
        'cmp85SourceFullGreenHybridAmplitudeConstantDraft_nonneg',
        'cmp85SourceFullGreen_ownerAmplitude_split_draft',
        'cmp85SourceFullGreen_ownerAmplitude_inverse_square_draft',
        'exists_cmp85SourceFullGreen_uniformOwnerAmplitude_draft')},
}


def sha(blob):
    return hashlib.sha256(blob).hexdigest()


def fetch(commit, path, expected):
    with urllib.request.urlopen(RAW + commit + '/' + path, timeout=60) as r:
        blob = r.read()
    if sha(blob) != expected:
        raise RuntimeError('TRANSPORT_HASH=' + path)
    return blob


def load(commit, path, expected, name):
    result = types.ModuleType(name)
    exec(compile(fetch(commit, path, expected), path, 'exec'), result.__dict__)
    return result


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--preceding-archive-sha256', required=True)
    args = p.parse_args()
    if LOGS.exists():
        raise RuntimeError('ALREADY_STARTED_NO_REEXECUTION')
    base = load('bab82db79c118ef64259bc50627170f11c2e187e',
        'scripts/colab_cmp99_generic_full_point_source_residue_hot.py',
        '36032ac8bb14bbf4a3a991c4ac394d0620aadcf1dd6f38e0749672f3e658c8a2', 'recording_base')
    if not ROOT.is_dir() or not (base.TOOLCHAIN / 'lake').is_file():
        raise RuntimeError('RETAINED_RUNTIME_REQUIRED')
    LOGS.mkdir()
    base.ROOT, base.LOGS, base.RECORDS = ROOT, LOGS, []
    os.environ['PATH'] = str(base.TOOLCHAIN) + os.pathsep + os.environ['PATH']
    status, error = 'FAIL', None
    try:
        previous = load('950ff77bcf022d6da2a0809543f1ecc652e6cc44',
            'scripts/colab_cmp85_full_green_hybrid_repro_v2.py',
            '525c1e58f5961b81daa96075ab11fffc1e20269db525808c6b786463a6b8e81a', 'previous_verifier')
        gate_blob = (ROOT / 'scripts/full_green_owner_exact_axiom_gate.py').read_bytes()
        if sha(gate_blob) != previous.GATE_HASH:
            raise RuntimeError('AXIOM_GATE_HASH')
        gate = previous.module(gate_blob, 'exact_gate')
        report = previous.verify(previous.read_archive(PREVIOUS_ARCHIVE,
            args.preceding_archive_sha256), gate)
        (LOGS / 'preceding-verification.json').write_text(json.dumps(report, sort_keys=True) + '\n')
        if Path('/content/f4-repro-v2-exit.txt').read_text().strip() != '0':
            raise RuntimeError('PRECEDING_CHILD_NOT_ZERO')
        if base.run('original_head', ['git', 'rev-parse', 'HEAD']).strip() != PREVIOUS_SOURCE:
            raise RuntimeError('RETAINED_HEAD')
        base.run('original_clean', ['git', 'diff', '--exit-code', 'HEAD', '--',
            'YangMills', 'lean-toolchain', 'lake-manifest.json'])
        if base.run('mathlib', ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD']).strip() != previous.MATHLIB:
            raise RuntimeError('MATHLIB_PIN')
        for path, digest in BLOBS.items():
            blob = fetch(SOURCE, path, digest)
            dest = ROOT / path
            if dest.exists() and dest.read_bytes() != blob:
                raise RuntimeError('EXISTING_SOURCE_DIFFERS=' + path)
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(blob)
            (LOGS / dest.name).write_bytes(blob)
        (LOGS / 'paths.txt').write_text('\n'.join(BLOBS) + '\n')
        base.run('text_guard', ['python3', 'scripts/check_lean_overlay_text.py',
            '--paths-from', str(LOGS / 'paths.txt')])
        base.run('import_guard', ['python3', 'scripts/check_lean_import_prefix.py', *BLOBS])
        base.run('materialize_scalar_definition', ['lake', 'build',
            'YangMills.RG.BalabanCMP99GeneratedFullPointSourceOwnerBound'])
        lean_path = base.run('lean_path', ['lake', 'env', 'printenv', 'LEAN_PATH']).strip()
        if not lean_path or '\n' in lean_path:
            raise RuntimeError('LEAN_PATH_FORMAT')
        # Lake's compiled YangMills namespace must win over ROOT/YangMills.
        # ROOT is appended only to resolve the temporary tmp.* modules.
        draft_lean_path = lean_path + os.pathsep + str(ROOT)
        output_hashes = {}
        for stage, path in zip(AUDITS, BLOBS):
            output = base.run(stage, ['env', 'LEAN_PATH=' + draft_lean_path,
                str(base.TOOLCHAIN / 'lean'), '-o', str(Path(path).with_suffix('.olean')), path])
            axioms = gate.exact_axioms(output, AUDITS[stage])
            (LOGS / (stage + '-axioms.json')).write_text(json.dumps(axioms, sort_keys=True) + '\n')
            compiled = ROOT / Path(path).with_suffix('.olean')
            if not compiled.is_file():
                raise RuntimeError('MISSING_COMPILED_OUTPUT=' + path)
            output_hashes[str(Path(path).with_suffix('.olean'))] = sha(compiled.read_bytes())
            (LOGS / 'compiled-output-hashes.json').write_text(json.dumps(output_hashes, sort_keys=True) + '\n')
        if sha(PREVIOUS_ARCHIVE.read_bytes()) != args.preceding_archive_sha256.lower():
            raise RuntimeError('PRECEDING_ARCHIVE_CHANGED')
        status = 'PASS'
    except Exception as exc:
        error = repr(exc)
        print('HOT_FIRST_ERROR=' + error, flush=True)
    evidence = dict(status=status, runner_rev=REV, retained_source=PREVIOUS_SOURCE,
        draft_source=SOURCE, source_blobs=BLOBS, records=base.RECORDS, error=error,
        previous_archive_sha256=args.preceding_archive_sha256,
        project_build_cache_reused=True, cold_seal=False,
        files={f.name: sha(f.read_bytes()) for f in sorted(LOGS.iterdir()) if f.is_file()})
    (LOGS / 'debug-evidence.json').write_text(json.dumps(evidence, sort_keys=True) + '\n')
    archive = Path(str(LOGS) + '.tar.gz')
    with tarfile.open(archive, 'w:gz') as tar:
        tar.add(LOGS, arcname=LOGS.name)
    print('HOT_ARCHIVE=' + str(archive), flush=True)
    print('HOT_ARCHIVE_SHA256=' + sha(archive.read_bytes()), flush=True)
    print('HOT_DEBUG_STATUS=' + status + ' COLD_SEAL=0', flush=True)
    return 0 if status == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
