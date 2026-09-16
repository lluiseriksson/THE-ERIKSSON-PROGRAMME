#!/usr/bin/env python3
"""Fresh cold gate for seventeen physical reflection modules and 52 declarations.

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

SOURCE = '84ceb5f2f466ab8f4e9dea175fd412c7bf63a21e'
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
    runner.RUNNER_REV = 'neumann-physical-reflection-promoted-cold-v1'
    runner.SOURCE_SHA = SOURCE
    base.SOURCE = SOURCE
    runner.ROOT = Path('/content/hrpoly-' + runner.RUNNER_REV)
    runner.EVIDENCE = Path(str(runner.ROOT) + '-evidence')
    runner.ARCHIVE = Path(str(runner.EVIDENCE) + '.tar.gz')
    runner.PATH_MANIFEST = Path(str(runner.ROOT) + '-paths.txt')
    runner.SOURCE_BLOBS = {
    "YangMills/RG/NeumannCoordinateProduct.lean": "e3134261f456bb7fbeb281555fbee1eb105222f029fd3852538fe024a290b063",
    "YangMills/RG/NeumannHalfCellPhase.lean": "609f23d4b42f74f6bebe14baf29e660a2e3baa84ae0871de7530fc46f07ca6f3",
    "YangMills/RG/NeumannEntireAverageHalfCellPhase.lean": "99787aaa76a666c6253c993464360fb15e66df7a986ebd4807a6928cb37767dc",
    "YangMills/RG/NeumannCoordinateAliasReflection.lean": "1366895c6bd328b89551736f7fffbc5ac3ba9023847f5d27348f5120a139e58e",
    "YangMills/RG/NeumannCoordinateMomentumCarry.lean": "7c589050ce3164a83d653060040ebe700dcbc7a52a4edbc6187d0c748c11010c",
    "YangMills/RG/NeumannCoordinateAveragePhase.lean": "cb9365fcb4420b7c11e091d5f590fc75f26c686e2b6d201e3822934195f6a2a5",
    "YangMills/RG/NeumannDiagonalTransport.lean": "8c5830c3f6d6831c8127a2c35347750511606f07dd584879f244a7ccc6987b4e",
    "YangMills/RG/NeumannActualCoordinateSolution.lean": "9693674859574bf98eefd16a56cfbd990ec4f74a93a94af1880045c48161993e",
    "YangMills/RG/NeumannCoordinateEndpointPhase.lean": "6227fb97a2cb2fb6f2da6af99fda3311860651a046f58a6333809ba1fe39705e",
    "YangMills/RG/NeumannActualCoordinateGreenIntegrand.lean": "83e50e61fc489152b141f2cae76621eb945c5fc4f01331ed458a90e8d4894c70",
    "YangMills/RG/NeumannCoordinateIntegralReflection.lean": "1a7e6aa9039fb06920b48f0293abb3f5a99dfd14c04342bf7061009b1b46b927",
    "YangMills/RG/NeumannPhysicalCoordinateReflectionDomain.lean": "6b53e16cb0aa084be8e344fedd398389fcfd30b2e4849c42a2f5e84a85f0a6af",
    "YangMills/RG/NeumannPhysicalCoordinateGreenIntegral.lean": "1e16c1e58897f0fdbec50ef744f4ea18fe2207a9ee3b8fe2ce2992612be12e3c",
    "YangMills/RG/NeumannActualFullSolutionScalar.lean": "989be0412c6e2b6075791fa974d50ab7d881375462f032d9b8ed20b9c6de34fc",
    "YangMills/RG/NeumannCommonBlockEndpointPhase.lean": "19f525a063fb6b3ebfdc961bd77cc52f6b13763f73c9c7fcd1a3f3985a91a8ae",
    "YangMills/RG/NeumannActualCommonBlockTranslation.lean": "05b8d49647821eac9df55152a2442512d4036343cb7b82c4b3ee41298a40db3d",
    "YangMills/RG/NeumannPhysicalHalfCellReflection.lean": "661ac7d2afa6ec90cfb5e394b795fe31f68bd9f3c3c710207864a5793cd457ac",
    "YangMills/RG/NeumannPhysicalHalfCellReflectionAudit.lean": "1f54e7170f39aa07c20a4be8f79d3a5dea5cd572274bb6dbef87eb01f90cc3f3"
}
    audit_names = {
    "reflection_audit": [
        "NeumannCoordinateProductRepro.one_factor",
        "NeumannHalfCellPhaseRepro.finite_exp_reverse",
        "YangMills.RG.neumannEntireAverageFactor_halfCellPhase",
        "YangMills.RG.neumannAliasPiCoordinateReflection_self",
        "YangMills.RG.neumannAliasPiCoordinateReflection_other",
        "YangMills.RG.neumannAliasCoordinateReflection_other",
        "YangMills.RG.neumannAliasCoordinateReflection_residue",
        "YangMills.RG.neumannAliasCoordinateReflection_involutive",
        "YangMills.RG.neumannAliasCoordinateReflection_sum",
        "YangMills.RG.neumannPhysicalAliasCoordinateReflection_central",
        "YangMills.RG.neumannMomentumCoordinateReflection_involutive",
        "YangMills.RG.neumannPhysicalAliasCoordinateReflection_momentum",
        "YangMills.RG.neumannEntireScaledLaplacianSymbol_coordinateReflection",
        "YangMills.RG.neumannEntireAliasFineSymbol_coordinateReflection",
        "YangMills.RG.neumannEntireAliasPrecisionMatrix_coordinateReflection",
        "YangMills.RG.neumannCoordinateHalfCellPhase_ne_zero",
        "YangMills.RG.neumannCoordinateHalfCellPhase_neg",
        "YangMills.RG.neumannEntireAverageAmplitude_coordinateReflection",
        "YangMills.RG.neumannEntireAliasAverageColumn_coordinateReflection",
        "YangMills.RG.neumannEntireAliasAverageRow_coordinateReflection",
        "NeumannDiagonalTransportRepro.action",
        "NeumannDiagonalTransportRepro.action_function",
        "NeumannDiagonalTransportRepro.solution_unique",
        "YangMills.RG.neumannActualCoordinatePrecision_action",
        "YangMills.RG.neumannActualCoordinateFullSolution_transport",
        "YangMills.RG.neumannFineEndpointCoordinateReflection_involutive",
        "YangMills.RG.neumannCoordinateEndpointPhase_identity",
        "YangMills.RG.neumannAliasTargetPhase_coordinateReflection",
        "YangMills.RG.neumannAliasSourcePhase_coordinateReflection",
        "YangMills.RG.neumannActualPointSource_coordinateTransport",
        "YangMills.RG.neumannActualPointSolution_coordinateReflection",
        "YangMills.RG.neumannActualFineGreenIntegrand_coordinateReflection",
        "YangMills.RG.neumannIntervalCoordinateReflection_insertNth",
        "YangMills.RG.neumannIntegral_coordinateReflection",
        "YangMills.RG.neumannCoordinateReflectedDomain_massUniform",
        "YangMills.RG.neumannPhysicalFineGreenIntegrand_coordinateReflection_massUniform",
        "YangMills.RG.neumannBrillouinMomentum_coordinateReflection",
        "YangMills.RG.neumannPhysicalGreen_coordinateReflection_massUniform",
        "YangMills.RG.neumannActualNoncentralSourceMoment_mul_right",
        "YangMills.RG.neumannActualFullSolutionMoment_mul_right",
        "YangMills.RG.neumannActualFullSolution_mul_right",
        "YangMills.RG.neumannAliasTargetPhase_blockShift",
        "YangMills.RG.neumannAliasSourcePhase_blockShift",
        "YangMills.RG.neumannCommonBlockPhase_cancel",
        "YangMills.RG.neumannActualPointSourceVector_blockShift",
        "YangMills.RG.neumannActualPointSourceSolution_blockShift",
        "YangMills.RG.neumannActualFineGreenIntegrand_commonBlockShift",
        "YangMills.RG.neumannActualPhysicalFineGreenIntegrand_commonBlockShift",
        "YangMills.RG.neumannActualNormalizedFineGreen_commonBlockShift",
        "YangMills.RG.neumannBlockBoundaryReflection_eq_center_shift",
        "YangMills.RG.neumannPhysicalGreen_blockBoundaryReflection_massUniform",
        "YangMills.RG.neumannPhysicalGreen_lowerHalfCellReflection_massUniform"
    ]
}
    audit_names = {stage: frozenset(names) for stage, names in audit_names.items()}
    base.EXPECTED = frozenset().union(*audit_names.values())
    runner.QUEUE = [
        ("reflection_focal", ["lake","build","YangMills.RG.NeumannPhysicalHalfCellReflection"], None),
        ("reflection_audit", ["lake","env","lean","YangMills/RG/NeumannPhysicalHalfCellReflectionAudit.lean"], audit_names["reflection_audit"]),
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
        (runner.EVIDENCE / 'neumann-physical-reflection-promoted-cold-contract.json').write_text(json.dumps({
            'source_sha': SOURCE,
            'parent_diagnostics': [{"source":"91dee187ebd5f32250c3966ed6a9141b25990ad7","archive_sha256":"8debebc3f16a117320c73c576451b5337994cf14ad0adca7d0db2dc4104e3883"}],
            'project_build_cache_restored': False,
            'durable_base_commit': BASE_SHA,
            'durable_base_sha256': '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892',
            'axiom_gate_sha256': '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
            'audit_expected': {stage: sorted(names) for stage, names in audit_names.items()},
            'queue': [stage for stage, _, _ in runner.QUEUE],
            'parser_self_test': {'accepted': 2, 'rejected': 9},
            'scope': 'literal arbitrary-depth full Green common block translation and coordinate half-cell reflection; not regional image equation, B0 or window15',
        }, sort_keys=True) + '\n', encoding='utf-8')
        outputs = {}
        for name in ["NeumannCoordinateProduct.olean","NeumannHalfCellPhase.olean","NeumannEntireAverageHalfCellPhase.olean","NeumannCoordinateAliasReflection.olean","NeumannCoordinateMomentumCarry.olean","NeumannCoordinateAveragePhase.olean","NeumannDiagonalTransport.olean","NeumannActualCoordinateSolution.olean","NeumannCoordinateEndpointPhase.olean","NeumannActualCoordinateGreenIntegrand.olean","NeumannCoordinateIntegralReflection.olean","NeumannPhysicalCoordinateReflectionDomain.olean","NeumannPhysicalCoordinateGreenIntegral.olean","NeumannActualFullSolutionScalar.olean","NeumannCommonBlockEndpointPhase.olean","NeumannActualCommonBlockTranslation.olean","NeumannPhysicalHalfCellReflection.olean"]:
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

