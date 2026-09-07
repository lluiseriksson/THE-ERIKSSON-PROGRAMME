#!/usr/bin/env python3
"""Fresh cold gate for five physical image-seam modules and eleven declarations.

No restoration of project build outputs. Stop on the first real child error.
This intermediate seal is not regional B0, window 15 or terminal hRpoly.
Runtime retained only to preserve and independently verify its evidence.
"""
from __future__ import annotations

import hashlib
import json
import shutil
from pathlib import Path
import types
import urllib.request

SOURCE = '0f43fbdc51650fb2e8d77282d1c3af18b7f406f0'
BASE_SHA = 'ddf6fdc1882edddbf063389aab4d455a8ed30801'
RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'


def load_module(sha, path, expected_hash, name):
    url = RAW + sha + '/' + path
    with urllib.request.urlopen(url, timeout=60) as response:
        blob = response.read()
    digest = hashlib.sha256(blob).hexdigest()
    print('TRANSPORT=' + path + ' SHA256=' + digest, flush=True)
    if digest != expected_hash:
        raise RuntimeError('TRANSPORT_HASH_MISMATCH=' + path)
    module = types.ModuleType(name)
    exec(compile(blob, url, 'exec'), module.__dict__)
    return module


def main():
    base = load_module(BASE_SHA,
        'scripts/colab_cmp99_full_green_arbitrary_residue_cold.py',
        '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892',
        'owner_consumers_durable_base')
    gate = load_module(SOURCE, 'scripts/full_green_owner_exact_axiom_gate.py',
        '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
        'owner_consumers_exact_gate')
    runner = base.runner
    runner.RUNNER_REV = 'neumann-physical-image-seam-promoted-cold-v1'
    runner.SOURCE_SHA = SOURCE
    base.SOURCE = SOURCE
    runner.ROOT = Path('/content/hrpoly-' + runner.RUNNER_REV)
    runner.EVIDENCE = Path(str(runner.ROOT) + '-evidence')
    runner.ARCHIVE = Path(str(runner.EVIDENCE) + '.tar.gz')
    runner.PATH_MANIFEST = Path(str(runner.ROOT) + '-paths.txt')
    runner.SOURCE_BLOBS = {
    "YangMills/RG/NeumannBoundaryOrbitPermutation.lean": "2ba5e1027f5001d13a6e12085f12fdc657ca93b282c0023e9cb3c3287edd3db8",
    "YangMills/RG/NeumannBoundaryImagePermutation.lean": "a606e92d9047df15bde1c81346215e5d62b5f1c0432d54b467cf14444d4fa9ee",
    "YangMills/RG/NeumannBoundaryImageSeriesReindex.lean": "fc753f8295d3cb41b574d4ca56da02d49ce094ed092ecd7419d08af51fa29830",
    "YangMills/RG/NeumannPhysicalBoundaryTransfer.lean": "05bb9598703fbe6dd0e7b5bfed4a3d5a64dcfa43813bb2214adcf7b02ee62606",
    "YangMills/RG/NeumannPhysicalImageSeam.lean": "87d7ea8497d7813f490b7eb070b93b5dc810f1b1d80dc707782fdac6fa36ac7c",
    "YangMills/RG/NeumannPhysicalImageSeamAudit.lean": "ff219ff5428e59f7445d80e6a95fc4e16c4a217eafad15dd3d2d1cfbace4e860"
}
    audit_names = {
    "seam_audit": [
        "YangMills.RG.neumannBoundaryOrbitIndexEquiv_involutive",
        "YangMills.RG.neumannBoundaryOrbitIndexEquiv_image",
        "YangMills.RG.neumannBoundaryImageIndexEquiv_involutive",
        "YangMills.RG.neumannBoundaryImageIndexEquiv_image",
        "YangMills.RG.neumannBoundaryImageIndexEquiv_factor",
        "YangMills.RG.neumannBoundaryImage_tsum_sum_reindex",
        "YangMills.RG.neumannBoundaryImage_reflected_source_sum",
        "YangMills.RG.neumannPhysicalGreen_blockBoundaryTransfer_massUniform",
        "YangMills.RG.neumannActualFullGreenImage_summable_boundaryInvariant",
        "YangMills.RG.neumannActualFullGreenImage_lowerGhost",
        "YangMills.RG.neumannActualFullGreenImage_upperGhost"
    ]
}
    audit_names = {stage: frozenset(names) for stage, names in audit_names.items()}
    base.EXPECTED = frozenset().union(*audit_names.values())
    runner.QUEUE = [
        ("seam_focal", ["lake","build","YangMills.RG.NeumannPhysicalImageSeam"], None),
        ("seam_audit", ["lake","env","lean","YangMills/RG/NeumannPhysicalImageSeamAudit.lean"], audit_names["seam_audit"]),
    ]

    def parse_axioms(output, expected):
        try:
            result = gate.exact_axioms(output, expected)
        except ValueError as error:
            # The pinned base preflight expects RuntimeError on deliberate
            # invalid-axiom fixtures; preserve the strict gate's rejection.
            raise RuntimeError(str(error)) from error
        print('AXIOM_GATE=PASS ' + json.dumps(result, sort_keys=True), flush=True)

    runner.parse_axioms = parse_axioms
    base.parse_axioms = parse_axioms
    previous_make_evidence = runner.make_evidence

    def make_evidence(status, opened):
        runner.EVIDENCE.mkdir(parents=True, exist_ok=True)
        (runner.EVIDENCE / 'neumann-physical-image-seam-promoted-cold-contract.json').write_text(json.dumps({
            'source_sha': SOURCE,
            'parent_diagnostics': [{"source":"970356bfc58ec2ca9ba94163be952d382c0689c9","archive_sha256":"cd7a66477087916e59c54bf0f6d995810ab838d10eedb7168ec3a7fc04e12977"}],
            'project_build_cache_restored': False,
            'durable_base_commit': BASE_SHA,
            'durable_base_sha256': '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892',
            'axiom_gate_sha256': '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
            'audit_expected': {stage: sorted(names) for stage, names in audit_names.items()},
            'queue': [stage for stage, _, _ in runner.QUEUE],
            'parser_self_test': {'accepted': 2, 'rejected': 9},
            'scope': 'literal physical all-reflecting source-image summability and lower/upper ghost seam with fine/block boundary dictionary; not mixed FULL directions, regional point-source equation, inverse, B0 or window15',
        }, sort_keys=True) + '\n', encoding='utf-8')
        outputs = {}
        for name in ["NeumannBoundaryOrbitPermutation.olean","NeumannBoundaryImagePermutation.olean","NeumannBoundaryImageSeriesReindex.olean","NeumannPhysicalBoundaryTransfer.olean","NeumannPhysicalImageSeam.olean"]:
            origin = runner.ROOT / '.lake/build/lib/lean/YangMills/RG' / name
            if origin.is_file():
                shutil.copyfile(origin, runner.EVIDENCE / name)
                outputs[name] = hashlib.sha256((runner.EVIDENCE / name).read_bytes()).hexdigest()
            elif status == 'PASS':
                raise RuntimeError('MISSING_PRODUCTION_OUTPUT=' + name)
        (runner.EVIDENCE / 'production-outputs.json').write_text(
            json.dumps(outputs, sort_keys=True) + '\n', encoding='utf-8')
        return previous_make_evidence(status, opened)

    runner.make_evidence = make_evidence
    if runner.ROOT.exists() or runner.EVIDENCE.exists() or runner.ARCHIVE.exists():
        raise RuntimeError('FRESH_RUN_REQUIRED_NO_REEXECUTION')
    gate.self_test()
    base.PREFLIGHT = base.preflight()
    from google.colab import runtime
    saved_unassign = runtime.unassign
    runtime.unassign = lambda: print('RUNTIME_RETAINED_FOR_EVIDENCE_DOWNLOAD=1', flush=True)
    try:
        return runner.main()
    finally:
        runtime.unassign = saved_unassign


if __name__ == '__main__':
    raise SystemExit(main())
