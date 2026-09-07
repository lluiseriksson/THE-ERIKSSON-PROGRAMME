#!/usr/bin/env python3
"""Fresh cold gate for the literal physical mixed series and its boundary identities.

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

SOURCE = 'a5811d5ddd78faf6fe638aa00db30276af826baf'
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
    runner.RUNNER_REV = 'neumann-physical-mixed-seam-promoted-cold-v1'
    runner.SOURCE_SHA = SOURCE
    base.SOURCE = SOURCE
    runner.ROOT = Path('/content/hrpoly-' + runner.RUNNER_REV)
    runner.EVIDENCE = Path(str(runner.ROOT) + '-evidence')
    runner.ARCHIVE = Path(str(runner.EVIDENCE) + '.tar.gz')
    runner.PATH_MANIFEST = Path(str(runner.ROOT) + '-paths.txt')
    runner.SOURCE_BLOBS = {
    "YangMills/RG/NeumannPhysicalMixedSeam.lean": "86bb135f617face75445e88a78f7906c596676fdb30fc900c47e453a9d2d3e79",
    "YangMills/RG/NeumannPhysicalMixedSeamAudit.lean": "a8e112a0aa4c90033c8fdb80f7a7799be2752abb7c4a387359c1dcc7f9a46fcb"
}
    audit_names = {
    "physical_seam_audit": [
        "YangMills.RG.summable_neumannPhysicalMixedGreenSeries",
        "YangMills.RG.neumannPhysicalMixedGreenSeries_periodic",
        "YangMills.RG.neumannPhysicalMixedGreenSeries_properBoundary"
    ]
}
    audit_names = {stage: frozenset(names) for stage, names in audit_names.items()}
    base.EXPECTED = frozenset().union(*audit_names.values())
    runner.QUEUE = [
        ("physical_seam_prerequisites", ["lake","build","YangMills.RG.NeumannMixedImageReindex","YangMills.RG.NeumannPhysicalFullFlag","YangMills.RG.NeumannPhysicalMixedSummability","YangMills.RG.NeumannPhysicalBoundaryTransfer"], None),
        ("physical_seam_focal", ["lake","build","YangMills.RG.NeumannPhysicalMixedSeam"], None),
        ("physical_seam_audit", ["lake","env","lean","YangMills/RG/NeumannPhysicalMixedSeamAudit.lean"], audit_names["physical_seam_audit"]),
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
        (runner.EVIDENCE / 'neumann-physical-mixed-seam-promoted-cold-contract.json').write_text(json.dumps({
            'source_sha': SOURCE,
            'parent_diagnostics': [{"source":"0d63d2b0f234d3780b60d6ce1242c6aa8e3f67ae","archive_sha256":"aed81d7fb9f7f55b197e0a21c71c4912591b45d3a6f8ea53b0f3218d0de5230c","overlay_sha256":"8b6a3b21158c3d047e76695c0da179511ae7d353a4be8c95a4da26726e73b155"}],
            'project_build_cache_restored': False,
            'durable_base_commit': BASE_SHA,
            'durable_base_sha256': '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892',
            'axiom_gate_sha256': '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
            'audit_expected': {stage: sorted(names) for stage, names in audit_names.items()},
            'queue': [stage for stage, _, _ in runner.QUEUE],
            'parser_self_test': {'accepted': 2, 'rejected': 9},
            'scope': 'literal physical complex Green mixed series with actual FULL flag: summability and periodic/PROPER boundary identities; not source equation, finite operator interchange, inverse, uniform B0 or window15',
        }, sort_keys=True) + '\n', encoding='utf-8')
        outputs = {}
        for name in ["NeumannPhysicalMixedSeam.olean"]:
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

