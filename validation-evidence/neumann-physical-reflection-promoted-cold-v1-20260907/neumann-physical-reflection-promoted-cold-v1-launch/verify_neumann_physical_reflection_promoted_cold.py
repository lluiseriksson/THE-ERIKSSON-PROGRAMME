#!/usr/bin/env python3
"""Exact 52-name physical reflection cold reader. Independent contract and output checks. No Lean, Git or subprocess calls.

The source checkout supplies two hash-pinned, side-effect-free helper modules.
Self-tests are synthetic metadata tests, never compilation evidence.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import math
from pathlib import Path
import types

SOURCE = '84ceb5f2f466ab8f4e9dea175fd412c7bf63a21e'
REV = 'neumann-physical-reflection-promoted-cold-v1'
ROOT = '/content/hrpoly-' + REV
BASE_HASH = '2f097a374361bd8e4c0f53220ffeeeb22fc06d6ccca5179aebda468d1aebee8e'
WRAPPER_HASH = '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892'
GATE_HASH = '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'
BLOBS = {
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
NAMES = {
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
NAMES = {s: set(names) for s, names in NAMES.items()}
COMMANDS = {
    "reflection_focal": [
        "lake",
        "build",
        "YangMills.RG.NeumannPhysicalHalfCellReflection"
    ],
    "reflection_audit": [
        "lake",
        "env",
        "lean",
        "YangMills/RG/NeumannPhysicalHalfCellReflectionAudit.lean"
    ]
}
REQUIRED = ['download_toolchain', 'extract_toolchain', 'lean_version', 'lake_version',
            'clone', 'checkout', 'head', 'overlay_text_guard', 'import_prefix_guard',
            'lake_update', 'mathlib_pin', 'cache_get', *COMMANDS]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def helper(folder, filename, expected):
    data = (folder / filename).read_bytes()
    require(sha(data) == expected, 'HELPER_HASH=' + filename)
    module = types.ModuleType(filename)
    exec(compile(data, filename, 'exec'), module.__dict__)
    return module


def verify(files, gate, old):
    data = json.loads(files['evidence.json'])
    expected = dict(source_sha=SOURCE, runner_rev=REV, status='PASS',
                    mathlib_sha=old.MATHLIB, toolchain_asset_sha256=old.ASSET,
                    source_blobs=BLOBS, minimum_ram_gib=40.0, gpu_runtime_authorized=False)
    for field, value in expected.items():
        require(data.get(field) == value, 'EVIDENCE_FIELD=' + field)
    contract = json.loads(files['gate-contract.json'])
    require(contract.get('source_sha') == SOURCE and
            contract.get('base_runner_sha256') == BASE_HASH and
            contract.get('project_build_cache_restored') is False and
            contract.get('expected_axiom_names') == sorted(set.union(*NAMES.values())),
            'GATE_CONTRACT')
    owner = json.loads(files['neumann-physical-reflection-promoted-cold-contract.json'])
    expected_owner = dict(source_sha=SOURCE,
            parent_diagnostics=[{"source":"91dee187ebd5f32250c3966ed6a9141b25990ad7","archive_sha256":"8debebc3f16a117320c73c576451b5337994cf14ad0adca7d0db2dc4104e3883"}],
        project_build_cache_restored=False,
            durable_base_commit='ddf6fdc1882edddbf063389aab4d455a8ed30801',
            durable_base_sha256=WRAPPER_HASH, axiom_gate_sha256=GATE_HASH,
            audit_expected={s: sorted(n) for s, n in NAMES.items()},
            queue=list(COMMANDS), scope="literal arbitrary-depth full Green common block translation and coordinate half-cell reflection; not regional image equation, B0 or window15", parser_self_test={'accepted': 2, 'rejected': 9})
    require(set(owner) == set(expected_owner), 'OWNER_CONTRACT_FIELDS')
    for field, value in expected_owner.items():
        require(owner.get(field) == value, 'OWNER_CONTRACT=' + field)
    preflight = json.loads(files['preflight.json'])
    require(len(preflight) == 2, 'PREFLIGHT_COUNT')
    for record, code in zip(preflight, (0, 7)):
        require(record['actual_exit'] == record['expected_exit'] == code and
                math.isfinite(record['seconds']) and record['seconds'] >= 0, 'PREFLIGHT')
    records = data['records']
    stages = [r['stage'] for r in records]
    require(len(stages) == len(set(stages)), 'DUPLICATE_STAGE')
    require([s for s in stages if s in REQUIRED] == REQUIRED, 'STAGE_ORDER')
    require(set(stages) <= set(REQUIRED) | {'apt_update', 'install_zstd'}, 'EXTRA_STAGE')
    expected_files = {'evidence.json', 'gate-contract.json', 'neumann-physical-reflection-promoted-cold-contract.json', 'preflight.json'}
    indexed = {}
    for r in records:
        stage = r['stage']
        indexed[stage] = r
        require(r.get('exit') == 0, 'EXIT=' + stage)
        require(isinstance(r.get('seconds'), (int, float)) and
                math.isfinite(r['seconds']) and r['seconds'] >= 0, 'TIME=' + stage)
        require(r.get('log_file') == stage + '.log', 'LOG_NAME=' + stage)
        require(sha(files[stage + '.log']) == r.get('output_sha256'), 'LOG_HASH=' + stage)
        require(json.loads(files[stage + '.json']) == r, 'RECORD=' + stage)
        expected_files |= {stage + '.log', stage + '.json'}
    production = json.loads(files['production-outputs.json'])
    require(set(production) == set(["NeumannCoordinateProduct.olean","NeumannHalfCellPhase.olean","NeumannEntireAverageHalfCellPhase.olean","NeumannCoordinateAliasReflection.olean","NeumannCoordinateMomentumCarry.olean","NeumannCoordinateAveragePhase.olean","NeumannDiagonalTransport.olean","NeumannActualCoordinateSolution.olean","NeumannCoordinateEndpointPhase.olean","NeumannActualCoordinateGreenIntegrand.olean","NeumannCoordinateIntegralReflection.olean","NeumannPhysicalCoordinateReflectionDomain.olean","NeumannPhysicalCoordinateGreenIntegral.olean","NeumannActualFullSolutionScalar.olean","NeumannCommonBlockEndpointPhase.olean","NeumannActualCommonBlockTranslation.olean","NeumannPhysicalHalfCellReflection.olean"]), 'PRODUCTION_OUTPUT_SET')
    for name, digest in production.items():
        require(sha(files[name]) == digest, 'PRODUCTION_OUTPUT_HASH=' + name)
    expected_files |= {'production-outputs.json', *production}
    require(set(files) == expected_files, 'FILE_SET')
    require(files['head.log'].decode().strip() == SOURCE, 'HEAD_LOG')
    require(files['mathlib_pin.log'].decode().strip() == old.MATHLIB, 'MATHLIB_LOG')
    for stage in ('lean_version', 'lake_version'):
        require('4.29.0-rc6' in files[stage + '.log'].decode(), 'VERSION=' + stage)
    require(indexed['checkout']['command'] == ['git', 'checkout', '--detach', SOURCE], 'CHECKOUT')
    for stage, cmd in COMMANDS.items():
        require(indexed[stage]['command'] == cmd and indexed[stage]['cwd'] == ROOT,
                'TARGET_COMMAND=' + stage)
    audits = {stage: gate.exact_axioms(files[stage + '.log'].decode(), names)
              for stage, names in NAMES.items()}
    return dict(status='PASS', source_sha=SOURCE, runner_rev=REV,
                stages_verified=len(records), audits=audits, production_outputs=production,
                evidence_json_file_sha256=sha(files['evidence.json']),
                evidence_json_payload_sha256=sha(files['evidence.json'].removesuffix(b'\n')),
                queue=[indexed[s] for s in COMMANDS])


def self_test(gate, old):
    gate.self_test()
    # Adapt the old synthetic fixture generator only to capture its fixture;
    # do not treat an old verifier PASS as evidence for the new contracts.
    captured = []
    original = old.verify_files
    def capture(files):
        captured.append(copy.deepcopy(files))
        return original(files)
    old.verify_files = capture
    old.self_test()
    old.verify_files = original
    files = captured[0]
    data = json.loads(files['evidence.json'])
    data.update(source_sha=SOURCE, runner_rev=REV, source_blobs=BLOBS)
    data['records'] = data['records'][:-2]
    for s in ('full_green_residue_focal', 'full_green_residue_audit'):
        del files[s + '.log'], files[s + '.json']
    for r in data['records']:
        r['cwd'] = ROOT
        if r['stage'] == 'checkout':
            r['command'] = ['git', 'checkout', '--detach', SOURCE]
    files['head.log'] = SOURCE.encode()
    for s, cmd in COMMANDS.items():
        text = 'synthetic only'
        if s in NAMES:
            text = '\n'.join(f"'{n}' does not depend on any axioms" if n.endswith('owner_bound')
                else f"'{n}' depends on axioms: [propext,\n Classical.choice, Quot.sound]"
                for n in sorted(NAMES[s]))
        files[s + '.log'] = text.encode()
        data['records'].append(dict(stage=s, exit=0, seconds=.01, command=cmd, cwd=ROOT,
                                   log_file=s + '.log', output_sha256=sha(text.encode())))
    for r in data['records']:
        r['output_sha256'] = sha(files[r['stage'] + '.log'])
        files[r['stage'] + '.json'] = json.dumps(r).encode()
    files['evidence.json'] = json.dumps(data).encode()
    contract = json.loads(files['gate-contract.json'])
    contract.update(source_sha=SOURCE, expected_axiom_names=sorted(set.union(*NAMES.values())))
    files['gate-contract.json'] = json.dumps(contract).encode()
    files['neumann-physical-reflection-promoted-cold-contract.json'] = json.dumps(dict(source_sha=SOURCE,
        parent_diagnostics=[{"source":"91dee187ebd5f32250c3966ed6a9141b25990ad7","archive_sha256":"8debebc3f16a117320c73c576451b5337994cf14ad0adca7d0db2dc4104e3883"}],
        project_build_cache_restored=False,
        durable_base_commit='ddf6fdc1882edddbf063389aab4d455a8ed30801',
        durable_base_sha256=WRAPPER_HASH, axiom_gate_sha256=GATE_HASH,
        audit_expected={s: sorted(n) for s,n in NAMES.items()}, queue=list(COMMANDS),
        scope="literal arbitrary-depth full Green common block translation and coordinate half-cell reflection; not regional image equation, B0 or window15", parser_self_test={'accepted':2,'rejected':9})).encode()
    production = {}
    for name in ["NeumannCoordinateProduct.olean","NeumannHalfCellPhase.olean","NeumannEntireAverageHalfCellPhase.olean","NeumannCoordinateAliasReflection.olean","NeumannCoordinateMomentumCarry.olean","NeumannCoordinateAveragePhase.olean","NeumannDiagonalTransport.olean","NeumannActualCoordinateSolution.olean","NeumannCoordinateEndpointPhase.olean","NeumannActualCoordinateGreenIntegrand.olean","NeumannCoordinateIntegralReflection.olean","NeumannPhysicalCoordinateReflectionDomain.olean","NeumannPhysicalCoordinateGreenIntegral.olean","NeumannActualFullSolutionScalar.olean","NeumannCommonBlockEndpointPhase.olean","NeumannActualCommonBlockTranslation.olean","NeumannPhysicalHalfCellReflection.olean"]:
        files[name] = ('synthetic output ' + name).encode()
        production[name] = sha(files[name])
    files['production-outputs.json'] = json.dumps(production).encode()
    verify(files, gate, old)
    bads = []
    bad = dict(files); bad[next(iter(production))] += b'corrupt'; bads.append(bad)
    bad = dict(files); del bad[next(iter(production))]; bads.append(bad)
    for field, value in [('source_sha', 'wrong'), ('status', 'FAIL')]:
        bad = dict(files); changed = copy.deepcopy(data); changed[field] = value
        bad['evidence.json'] = json.dumps(changed).encode(); bads.append(bad)
    bad = dict(files); bad['head.log'] += b'corrupt'; bads.append(bad)
    for word in ('sorryAx', 'ofReduceBool', 'Other.axiom'):
        bad = dict(files); changed = copy.deepcopy(data)
        stage = 'reflection_audit'
        bad[stage + '.log'] = bad[stage + '.log'].replace(b'Quot.sound', word.encode())
        changed['records'][-1]['output_sha256'] = sha(bad[stage + '.log'])
        bad[stage + '.json'] = json.dumps(changed['records'][-1]).encode()
        bad['evidence.json'] = json.dumps(changed).encode(); bads.append(bad)
    for bad in bads:
        try:
            verify(bad, gate, old)
        except (ValueError, RuntimeError, KeyError):
            continue
        raise ValueError('NEGATIVE_SELF_TEST_ACCEPTED')
    print('NEUMANN_PHYSICAL_REFLECTION_VERIFIER_SELF_TEST=PASS synthetic=1 rejected=' + str(len(bads)))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--helpers', type=Path, required=True)
    parser.add_argument('--self-test', action='store_true')
    parser.add_argument('--archive', type=Path)
    parser.add_argument('--sha256')
    args = parser.parse_args()
    old = helper(args.helpers, 'verify_cmp99_full_green_residue_cold.py',
                 '558295bb43e74bdae3eb6508656e7b8cde756cb393376320d0c197347396a02c')
    gate = helper(args.helpers, 'full_green_owner_exact_axiom_gate.py', GATE_HASH)
    if args.self_test:
        self_test(gate, old)
        return
    require(args.archive is not None and args.sha256, 'ARCHIVE_AND_HASH_REQUIRED')
    old.PREFIX = 'hrpoly-' + REV + '-evidence'
    report = verify(old.read_archive(args.archive, args.sha256), gate, old)
    report['archive_sha256'] = args.sha256.lower()
    print(json.dumps(report, sort_keys=True, indent=2))
    print('NEUMANN_PHYSICAL_REFLECTION_COLD_EVIDENCE_VERIFIED')


if __name__ == '__main__':
    main()

