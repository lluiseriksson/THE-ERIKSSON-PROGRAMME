#!/usr/bin/env python3
"""Fresh cold gate for the promoted F5 point/fibre prefix graph.

No restoration of project build outputs. Stop on the first real child error.
This intermediate seal is not regional B0, window 15 or terminal hRpoly.
Runtime retained only to preserve and independently verify its evidence.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import types
import urllib.request

SOURCE = '6c49a8daeb6d6c6f60ac4a2cd2bafda67a495ff4'
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
    runner.RUNNER_REV = 'cmp99-point-fibre-promoted-cold-v1'
    runner.SOURCE_SHA = SOURCE
    base.SOURCE = SOURCE
    runner.ROOT = Path('/content/hrpoly-' + runner.RUNNER_REV)
    runner.EVIDENCE = Path(str(runner.ROOT) + '-evidence')
    runner.ARCHIVE = Path(str(runner.EVIDENCE) + '.tar.gz')
    runner.PATH_MANIFEST = Path(str(runner.ROOT) + '-paths.txt')
    runner.SOURCE_BLOBS = {
        "YangMills/RG/FinitePiLpRealSliceFibreTransport.lean": "8beb2ed1c854782c3d1c5307b6138a8b3244fab3647072abca85e1c0127cc053",
        "YangMills/RG/FinitePiLpRealSliceFibreTransportAudit.lean": "e8a8ccca36cef4d144588d24dbe6db03266d746f784fb1ec92e94e3222a99449",
        "YangMills/RG/BalabanCMP99SourceFlowFullPointSourceFibreBound.lean": "a9c4309f8789b910c76facfca77866677e942a812df9d0e5614ca1daae49fb97",
        "YangMills/RG/BalabanCMP99SourceFlowFullPointSourceFibreBoundAudit.lean": "2683d18504d8caa8687e027fcc98553e1044f760e5406c6b1c801fe892028fc8",
        "YangMills/RG/FinitePiLpOwnerFibreAction.lean": "46b52c8ef7183dcfc77e64b8150f0b483ee4ba1383279d52d889edb32018c94d",
        "YangMills/RG/FinitePiLpOwnerFibreActionAudit.lean": "16ea84cf7885a6a9f0637377c19a94682900479dd9c8bd524ac932a34ac16519"
    }
    audit_names = {
        "real_slice_audit": [
            "YangMills.RG.norm_cmp99SUNLieCoordComplexificationLM",
            "YangMills.RG.norm_finitePiLpComplexOfReal_apply",
            "YangMills.RG.finitePiLpCanonicalComplexificationOuterCLM_ofReal",
            "YangMills.RG.norm_finitePiLpCanonicalComplexificationOuterCLM_ofReal_apply"
        ],
        "point_fibre_audit": [
            "YangMills.RG.norm_euclidean_of_common_scalar",
            "YangMills.RG.norm_cmp99SourceFlowFullPointSourceGreen_fibre_le_owner"
        ],
        "owner_action_audit": [
            "YangMills.RG.finitePiLpTypedBlockLocalizedSupBound_of_kernel_fibre_card"
        ]
    }
    audit_names = {stage: frozenset(names) for stage, names in audit_names.items()}
    base.EXPECTED = frozenset().union(*audit_names.values())
    runner.QUEUE = [
        ("real_slice_focal", ["lake","build","YangMills.RG.FinitePiLpRealSliceFibreTransport"], None),
        ("real_slice_audit", ["lake","env","lean","YangMills/RG/FinitePiLpRealSliceFibreTransportAudit.lean"], audit_names["real_slice_audit"]),
        ("point_fibre_focal", ["lake","build","YangMills.RG.BalabanCMP99SourceFlowFullPointSourceFibreBound"], None),
        ("point_fibre_audit", ["lake","env","lean","YangMills/RG/BalabanCMP99SourceFlowFullPointSourceFibreBoundAudit.lean"], audit_names["point_fibre_audit"]),
        ("owner_action_focal", ["lake","build","YangMills.RG.FinitePiLpOwnerFibreAction"], None),
        ("owner_action_audit", ["lake","env","lean","YangMills/RG/FinitePiLpOwnerFibreActionAudit.lean"], audit_names["owner_action_audit"]),
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
        (runner.EVIDENCE / 'f5-point-fibre-cold-contract.json').write_text(json.dumps({
            'source_sha': SOURCE,
            'parent_diagnostic_source': 'cee1f6d36ea8d81c5f301860f0a349b14efac47d',
            'parent_diagnostic_archive_sha256': '32db6f6e1e2c260f4014397084693ecb8b727ebfcc4af2cbcd469fc13ff063df',
            'project_build_cache_restored': False,
            'durable_base_commit': BASE_SHA,
            'durable_base_sha256': '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892',
            'axiom_gate_sha256': '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
            'audit_expected': {stage: sorted(names) for stage, names in audit_names.items()},
            'queue': [stage for stage, _, _ in runner.QUEUE],
            'parser_self_test': {'accepted': 2, 'rejected': 9},
            'scope': 'promoted F5 real-slice, point-fibre and generic owner action; not physical regional/derivative B0 or window15',
        }, sort_keys=True) + '\n', encoding='utf-8')
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

