#!/usr/bin/env python3
"""Fresh cold gate for nine promoted physical Green/owner/point identities.

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

SOURCE = 'b2d5df8ad6d600317b267bf87522a8bf472e9ea0'
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
    runner.RUNNER_REV = 'cmp99-physical-prefix-promoted-cold-v1'
    runner.SOURCE_SHA = SOURCE
    base.SOURCE = SOURCE
    runner.ROOT = Path('/content/hrpoly-' + runner.RUNNER_REV)
    runner.EVIDENCE = Path(str(runner.ROOT) + '-evidence')
    runner.ARCHIVE = Path(str(runner.EVIDENCE) + '.tar.gz')
    runner.PATH_MANIFEST = Path(str(runner.ROOT) + '-paths.txt')
    runner.SOURCE_BLOBS = {
        "YangMills/RG/BalabanCMP99SourceFlowPhysicalGreenRealSlice.lean": "fd2f19c59a4cc86d7e5c02f78ac40d5f74d0750e15b4832b6fff76d2d16cef0e",
        "YangMills/RG/BalabanCMP99SourceFlowPhysicalGreenRealSliceAudit.lean": "65b6a28f8415f9370c2bc874fc8ed9b3239b725ba7f52283eede116326b0e208",
        "YangMills/RG/BalabanCMP99SourceFlowPhysicalOwnerDictionary.lean": "0a0adacc931bf7cf9be7c6a85e9589715adb29336791a8d798020b060f6debf3",
        "YangMills/RG/BalabanCMP99SourceFlowPhysicalOwnerDictionaryAudit.lean": "bc0b2519dbbbc9f5aeddfb0d7237b053d7f63a6167570b3b2efe99d2d9d43442",
        "YangMills/RG/BalabanCMP99SourceFlowPhysicalPointProbe.lean": "a8289d1736931247ad03ab9e73032192d4fcd26f2f5fa126a21366b677d2aa7a",
        "YangMills/RG/BalabanCMP99SourceFlowPhysicalPointProbeAudit.lean": "e9c52c50201157dd163aecdc8cc32bbd73ec204f0a65f109067218b917394385"
    }
    audit_names = {
        "real_slice_audit": [
            "YangMills.RG.cmp99SourceFlowPhysicalAmbientGreen_ofReal",
            "YangMills.RG.cmp99SourceFlowPhysicalStep7bFieldEquiv_apply_site",
            "YangMills.RG.cmp99SourceFlowPhysicalStep7bGreen_ofReal",
            "YangMills.RG.norm_cmp99SourceFlowPhysicalStep7bGreen_ofReal_apply"
        ],
        "owner_dictionary_audit": [
            "YangMills.RG.cmp99PhysicalStep7bSiteEquiv_eq_sourceLocalization",
            "YangMills.RG.cmp99PhysicalStep7b_blockSite_eq_sourceLocalizationOwner",
            "YangMills.RG.card_cmp99SourceLocalizationOwner_fibre"
        ],
        "point_probe_audit": [
            "YangMills.RG.cmp99ComplexOuter_singleFinitePiLp_eq_pointSource",
            "YangMills.RG.cmp99PhysicalStep7b_complexSingle_eq_pointSource"
        ]
    }
    audit_names = {stage: frozenset(names) for stage, names in audit_names.items()}
    base.EXPECTED = frozenset().union(*audit_names.values())
    runner.QUEUE = [
        ("real_slice_focal", ["lake","build","YangMills.RG.BalabanCMP99SourceFlowPhysicalGreenRealSlice"], None),
        ("real_slice_audit", ["lake","env","lean","YangMills/RG/BalabanCMP99SourceFlowPhysicalGreenRealSliceAudit.lean"], audit_names["real_slice_audit"]),
        ("owner_dictionary_focal", ["lake","build","YangMills.RG.BalabanCMP99SourceFlowPhysicalOwnerDictionary"], None),
        ("owner_dictionary_audit", ["lake","env","lean","YangMills/RG/BalabanCMP99SourceFlowPhysicalOwnerDictionaryAudit.lean"], audit_names["owner_dictionary_audit"]),
        ("point_probe_focal", ["lake","build","YangMills.RG.BalabanCMP99SourceFlowPhysicalPointProbe"], None),
        ("point_probe_audit", ["lake","env","lean","YangMills/RG/BalabanCMP99SourceFlowPhysicalPointProbeAudit.lean"], audit_names["point_probe_audit"]),
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
        (runner.EVIDENCE / 'f5-physical-prefix-cold-contract.json').write_text(json.dumps({
            'source_sha': SOURCE,
            'parent_diagnostic_source': '91cc4dd5d6133e0eb0fc59279d58a71487caa6c7',
            'parent_diagnostic_archive_sha256': '21dc287d46f7fbef95c043a443e835d7805f32469d77691af405044c2a391a73',
            'project_build_cache_restored': False,
            'durable_base_commit': BASE_SHA,
            'durable_base_sha256': '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892',
            'axiom_gate_sha256': '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
            'audit_expected': {stage: sorted(names) for stage, names in audit_names.items()},
            'queue': [stage for stage, _, _ in runner.QUEUE],
            'parser_self_test': {'accepted': 2, 'rejected': 9},
            'scope': 'promoted literal physical Green real-slice, owner dictionary and whole-vector point probe; not regional/derivative B0 or window15',
        }, sort_keys=True) + '\n', encoding='utf-8')
        outputs = {}
        for name in ["BalabanCMP99SourceFlowPhysicalGreenRealSlice.olean","BalabanCMP99SourceFlowPhysicalOwnerDictionary.olean","BalabanCMP99SourceFlowPhysicalPointProbe.olean"]:
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
