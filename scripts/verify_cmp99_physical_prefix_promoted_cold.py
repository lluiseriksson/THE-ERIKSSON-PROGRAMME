#!/usr/bin/env python3
"""Read-only promoted physical prefix cold-graph evidence verifier. No Lean, Git or subprocess calls.

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

SOURCE = 'b2d5df8ad6d600317b267bf87522a8bf472e9ea0'
REV = 'cmp99-physical-prefix-promoted-cold-v1'
ROOT = '/content/hrpoly-' + REV
BASE_HASH = '2f097a374361bd8e4c0f53220ffeeeb22fc06d6ccca5179aebda468d1aebee8e'
WRAPPER_HASH = '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892'
GATE_HASH = '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'
BLOBS = {
    "YangMills/RG/BalabanCMP99SourceFlowPhysicalGreenRealSlice.lean": "fd2f19c59a4cc86d7e5c02f78ac40d5f74d0750e15b4832b6fff76d2d16cef0e",
    "YangMills/RG/BalabanCMP99SourceFlowPhysicalGreenRealSliceAudit.lean": "65b6a28f8415f9370c2bc874fc8ed9b3239b725ba7f52283eede116326b0e208",
    "YangMills/RG/BalabanCMP99SourceFlowPhysicalOwnerDictionary.lean": "0a0adacc931bf7cf9be7c6a85e9589715adb29336791a8d798020b060f6debf3",
    "YangMills/RG/BalabanCMP99SourceFlowPhysicalOwnerDictionaryAudit.lean": "bc0b2519dbbbc9f5aeddfb0d7237b053d7f63a6167570b3b2efe99d2d9d43442",
    "YangMills/RG/BalabanCMP99SourceFlowPhysicalPointProbe.lean": "a8289d1736931247ad03ab9e73032192d4fcd26f2f5fa126a21366b677d2aa7a",
    "YangMills/RG/BalabanCMP99SourceFlowPhysicalPointProbeAudit.lean": "e9c52c50201157dd163aecdc8cc32bbd73ec204f0a65f109067218b917394385"
}
NAMES = {
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
NAMES = {s: set(names) for s, names in NAMES.items()}
COMMANDS = {
    "real_slice_focal": [
        "lake",
        "build",
        "YangMills.RG.BalabanCMP99SourceFlowPhysicalGreenRealSlice"
    ],
    "real_slice_audit": [
        "lake",
        "env",
        "lean",
        "YangMills/RG/BalabanCMP99SourceFlowPhysicalGreenRealSliceAudit.lean"
    ],
    "owner_dictionary_focal": [
        "lake",
        "build",
        "YangMills.RG.BalabanCMP99SourceFlowPhysicalOwnerDictionary"
    ],
    "owner_dictionary_audit": [
        "lake",
        "env",
        "lean",
        "YangMills/RG/BalabanCMP99SourceFlowPhysicalOwnerDictionaryAudit.lean"
    ],
    "point_probe_focal": [
        "lake",
        "build",
        "YangMills.RG.BalabanCMP99SourceFlowPhysicalPointProbe"
    ],
    "point_probe_audit": [
        "lake",
        "env",
        "lean",
        "YangMills/RG/BalabanCMP99SourceFlowPhysicalPointProbeAudit.lean"
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
    owner = json.loads(files['f5-physical-prefix-cold-contract.json'])
    for field, value in dict(source_sha=SOURCE,
            parent_diagnostic_source='91cc4dd5d6133e0eb0fc59279d58a71487caa6c7',
        parent_diagnostic_archive_sha256='21dc287d46f7fbef95c043a443e835d7805f32469d77691af405044c2a391a73',
        project_build_cache_restored=False,
            durable_base_commit='ddf6fdc1882edddbf063389aab4d455a8ed30801',
            durable_base_sha256=WRAPPER_HASH, axiom_gate_sha256=GATE_HASH,
            audit_expected={s: sorted(n) for s, n in NAMES.items()},
            queue=list(COMMANDS), parser_self_test={'accepted': 2, 'rejected': 9}).items():
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
    expected_files = {'evidence.json', 'gate-contract.json', 'f5-physical-prefix-cold-contract.json', 'preflight.json'}
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
    require(set(production) == set(["BalabanCMP99SourceFlowPhysicalGreenRealSlice.olean","BalabanCMP99SourceFlowPhysicalOwnerDictionary.olean","BalabanCMP99SourceFlowPhysicalPointProbe.olean"]), 'PRODUCTION_OUTPUT_SET')
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
    files['f5-physical-prefix-cold-contract.json'] = json.dumps(dict(source_sha=SOURCE,
        parent_diagnostic_source='91cc4dd5d6133e0eb0fc59279d58a71487caa6c7',
        parent_diagnostic_archive_sha256='21dc287d46f7fbef95c043a443e835d7805f32469d77691af405044c2a391a73',
        project_build_cache_restored=False,
        durable_base_commit='ddf6fdc1882edddbf063389aab4d455a8ed30801',
        durable_base_sha256=WRAPPER_HASH, axiom_gate_sha256=GATE_HASH,
        audit_expected={s: sorted(n) for s,n in NAMES.items()}, queue=list(COMMANDS),
        parser_self_test={'accepted':2,'rejected':9})).encode()
    production = {}
    for name in ["BalabanCMP99SourceFlowPhysicalGreenRealSlice.olean","BalabanCMP99SourceFlowPhysicalOwnerDictionary.olean","BalabanCMP99SourceFlowPhysicalPointProbe.olean"]:
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
        stage = 'point_probe_audit'
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
    print('F5_PHYSICAL_PREFIX_VERIFIER_SELF_TEST=PASS synthetic=1 rejected=' + str(len(bads)))


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
    print('F5_PHYSICAL_PREFIX_COLD_EVIDENCE_VERIFIED')


if __name__ == '__main__':
    main()
