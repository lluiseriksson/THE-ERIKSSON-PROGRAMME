#!/usr/bin/env python3
"""Fresh cold cohort for five rectangle and three actual full-G declarations.

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

SOURCE = 'd9d1bcae8e53b2ad442f507de0d695a1c5e0ccd6'
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
    runner.RUNNER_REV = 'neumann-rectangle-full-green-cohort-cold-v1'
    runner.SOURCE_SHA = SOURCE
    base.SOURCE = SOURCE
    runner.ROOT = Path('/content/hrpoly-' + runner.RUNNER_REV)
    runner.EVIDENCE = Path(str(runner.ROOT) + '-evidence')
    runner.ARCHIVE = Path(str(runner.EVIDENCE) + '.tar.gz')
    runner.PATH_MANIFEST = Path(str(runner.ROOT) + '-paths.txt')
    runner.SOURCE_BLOBS = {
    "YangMills/RG/NeumannImageRectangleCoverage.lean": "c8570a36430554fa608a3e1b483b7a3baed6bb6fd26f34f5995e71290d477aee",
    "YangMills/RG/NeumannImageRectangleCoverageAudit.lean": "df0dbdde47edacbe9bf7d9fd82f2a30a75f94f436452a217346dc2df947429ce",
    "YangMills/RG/NeumannActualFullGreenReflectionSummability.lean": "8b8129eb1c155e576cefaeceb2227a1d9878a801a80e7426213c5b1c1fcd16f2",
    "YangMills/RG/NeumannActualFullGreenReflectionSummabilityAudit.lean": "4181611e3d0f44c863e25d6863bec1b19ce0db394f17db9a620bbc66b17c3ca1"
}
    audit_names = {
    "rectangle_audit": [
        "YangMills.RG.neumannImageRectangleCoordinateEquiv",
        "YangMills.RG.neumannImageRectangleIndexEquiv_apply",
        "YangMills.RG.neumannImageRectangleFamilyEquiv_apply",
        "YangMills.RG.neumannImageRectangleFamily_bijective",
        "YangMills.RG.neumannImageRectangle_fixedPoint_injective"
    ],
    "full_green_audit": [
        "YangMills.RG.neumannActualFullGreenDecayCertificate",
        "YangMills.RG.summable_neumannActualFullGreenReflection_sum",
        "YangMills.RG.summable_neumannActualFullGreenReflection_real_sum"
    ]
}
    audit_names = {stage: frozenset(names) for stage, names in audit_names.items()}
    base.EXPECTED = frozenset().union(*audit_names.values())
    runner.QUEUE = [
        ("rectangle_focal", ["lake","build","YangMills.RG.NeumannImageRectangleCoverage"], None),
        ("rectangle_audit", ["lake","env","lean","YangMills/RG/NeumannImageRectangleCoverageAudit.lean"], audit_names["rectangle_audit"]),
        ("full_green_focal", ["lake","build","YangMills.RG.NeumannActualFullGreenReflectionSummability"], None),
        ("full_green_audit", ["lake","env","lean","YangMills/RG/NeumannActualFullGreenReflectionSummabilityAudit.lean"], audit_names["full_green_audit"]),
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
        (runner.EVIDENCE / 'neumann-rectangle-full-green-cohort-cold-contract.json').write_text(json.dumps({
            'source_sha': SOURCE,
            'parent_diagnostic_source': 'fbf2e61f38afbe050200a0c7aa275b46ae45a924',
            'physical_diagnostic_source': 'acc09ce87687c473f7fc8280e6d61c78e2d24f7e',
            'physical_diagnostic_archive_sha256': 'b00bfb901dc0559f5ca13942cc1f5ec2a64749af0bfd37bd26f3310c9c1f4e03',
            'parent_diagnostic_archive_sha256': 'aae64e9f3eb9966b7bfe1c90398e9460608082c2d3388fa4e2a67d2639f01f2e',
            'project_build_cache_restored': False,
            'durable_base_commit': BASE_SHA,
            'durable_base_sha256': '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892',
            'axiom_gate_sha256': '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
            'audit_expected': {stage: sorted(names) for stage, names in audit_names.items()},
            'queue': [stage for stage, _, _ in runner.QUEUE],
            'parser_self_test': {'accepted': 2, 'rejected': 9},
            'scope': 'multidimensional rectangle image coverage plus actual full Eq246 source-image summability; not inverse, B0 or window15',
        }, sort_keys=True) + '\n', encoding='utf-8')
        outputs = {}
        for name in ["NeumannImageRectangleCoverage.olean", "NeumannActualFullGreenReflectionSummability.olean"]:
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
