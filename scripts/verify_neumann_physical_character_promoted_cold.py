#!/usr/bin/env python3
"""Exact six-name physical character cold reader. Independent contract and output checks. No Lean, Git or subprocess calls.

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

SOURCE = '29a48ac4bb1058cd71b74f65029e918d49e74b60'
REV = 'neumann-physical-character-promoted-cold-v1'
ROOT = '/content/hrpoly-' + REV
BASE_HASH = '2f097a374361bd8e4c0f53220ffeeeb22fc06d6ccca5179aebda468d1aebee8e'
WRAPPER_HASH = '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892'
GATE_HASH = '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'
BLOBS = {
    "YangMills/RG/NeumannAliasPrecisionReadout.lean": "216c2218483217be2ea18cfba1e9567246d051776f5080acf718fedee51e0a85",
    "YangMills/RG/NeumannAliasPrecisionReadoutAudit.lean": "ce59a432bfdc298ad804eb8ed2329892ac10f7e43a5b88a71918f3e6766a1e95",
    "YangMills/RG/NeumannMaskedDifference.lean": "976c3f090fd8d5f0e73c11d40f65956f30b5b0bba500ecd0c795ca822a505c45",
    "YangMills/RG/NeumannMaskedDifferenceAudit.lean": "600aa41bcfc8915cdb894d63b699ef20e1e041da7afa60689d88b58b10b16b62",
    "YangMills/RG/NeumannPhysicalBrillouinCharacter.lean": "a065cba1db9858fb9b34f53183026dc3fd39db07f41153c36a770764a3151c84",
    "YangMills/RG/NeumannPhysicalBrillouinCharacterAudit.lean": "52242ac12b71238d916729072871802710f04c36d20593ed327afa7ca2afa57f"
}
NAMES = {
    "mask_audit": [
        "YangMills.RG.neumannMaskedForwardDifference",
        "YangMills.RG.neumannMaskedBackwardDifference"
    ],
    "physical_audit": [
        "YangMills.RG.neumannTorus_volumeCharacterIntegral",
        "YangMills.RG.neumannPhysicalBrillouin_character_phase",
        "YangMills.RG.neumannPhysicalBrillouin_integerCharacterIntegral"
    ],
    "readout_audit": [
        "YangMills.RG.neumannAliasPrecision_finePointSource_readout"
    ]
}
NAMES = {s: set(names) for s, names in NAMES.items()}
COMMANDS = {
    "mask_focal": [
        "lake",
        "build",
        "YangMills.RG.NeumannMaskedDifference"
    ],
    "mask_audit": [
        "lake",
        "env",
        "lean",
        "YangMills/RG/NeumannMaskedDifferenceAudit.lean"
    ],
    "physical_focal": [
        "lake",
        "build",
        "YangMills.RG.NeumannPhysicalBrillouinCharacter"
    ],
    "physical_audit": [
        "lake",
        "env",
        "lean",
        "YangMills/RG/NeumannPhysicalBrillouinCharacterAudit.lean"
    ],
    "readout_focal": [
        "lake",
        "build",
        "YangMills.RG.NeumannAliasPrecisionReadout"
    ],
    "readout_audit": [
        "lake",
        "env",
        "lean",
        "YangMills/RG/NeumannAliasPrecisionReadoutAudit.lean"
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
    owner = json.loads(files['neumann-physical-character-promoted-cold-contract.json'])
    expected_owner = dict(source_sha=SOURCE,
            parent_diagnostics=[{"source":"98f4337e06271a7d5e3957450440292db0f79168","archive_sha256":"2b8c8aa39332e863f79a90fbbcdaaa559caa4ce8108cb027353d7e04e6ad4780","source_blobs":{"tmp/NeumannMaskedDifferenceRepro.lean":"70903fca9cf0e0510bf300f8e77b01d97da5bcd2d1b165adce98cea037814b09"}},{"source":"ce9cc5cc858214ee4e80fca27e6854d22567f653","archive_sha256":"a6618a294b75d5437093bc859f802273889fa9170f092395dc2d1e5156dac3e1","source_blobs":{"tmp/NeumannPhysicalBrillouinCharacterDraft.lean":"c845da5c7961927047d0e8974031d2ff29c7791d7be8bb6113c99f16dc44dc75","tmp/NeumannAliasPrecisionReadoutDraft.lean":"ddcc7a677396a175bea22e002304b00fe4c9b89de52f2714605eb59b3f5e2274"}}],
        project_build_cache_restored=False,
            durable_base_commit='ddf6fdc1882edddbf063389aab4d455a8ed30801',
            durable_base_sha256=WRAPPER_HASH, axiom_gate_sha256=GATE_HASH,
            audit_expected={s: sorted(n) for s, n in NAMES.items()},
            queue=list(COMMANDS), scope="masked endpoint differences, literal physical character integral and alias precision readout; not actual finite operator action, counting inverse, uniform B0 or window15", parser_self_test={'accepted': 2, 'rejected': 9})
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
    expected_files = {'evidence.json', 'gate-contract.json', 'neumann-physical-character-promoted-cold-contract.json', 'preflight.json'}
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
    require(set(production) == set(["NeumannMaskedDifference.olean","NeumannPhysicalBrillouinCharacter.olean","NeumannAliasPrecisionReadout.olean"]), 'PRODUCTION_OUTPUT_SET')
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
    files['neumann-physical-character-promoted-cold-contract.json'] = json.dumps(dict(source_sha=SOURCE,
        parent_diagnostics=[{"source":"98f4337e06271a7d5e3957450440292db0f79168","archive_sha256":"2b8c8aa39332e863f79a90fbbcdaaa559caa4ce8108cb027353d7e04e6ad4780","source_blobs":{"tmp/NeumannMaskedDifferenceRepro.lean":"70903fca9cf0e0510bf300f8e77b01d97da5bcd2d1b165adce98cea037814b09"}},{"source":"ce9cc5cc858214ee4e80fca27e6854d22567f653","archive_sha256":"a6618a294b75d5437093bc859f802273889fa9170f092395dc2d1e5156dac3e1","source_blobs":{"tmp/NeumannPhysicalBrillouinCharacterDraft.lean":"c845da5c7961927047d0e8974031d2ff29c7791d7be8bb6113c99f16dc44dc75","tmp/NeumannAliasPrecisionReadoutDraft.lean":"ddcc7a677396a175bea22e002304b00fe4c9b89de52f2714605eb59b3f5e2274"}}],
        project_build_cache_restored=False,
        durable_base_commit='ddf6fdc1882edddbf063389aab4d455a8ed30801',
        durable_base_sha256=WRAPPER_HASH, axiom_gate_sha256=GATE_HASH,
        audit_expected={s: sorted(n) for s,n in NAMES.items()}, queue=list(COMMANDS),
        scope="masked endpoint differences, literal physical character integral and alias precision readout; not actual finite operator action, counting inverse, uniform B0 or window15", parser_self_test={'accepted':2,'rejected':9})).encode()
    production = {}
    for name in ["NeumannMaskedDifference.olean","NeumannPhysicalBrillouinCharacter.olean","NeumannAliasPrecisionReadout.olean"]:
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
        stage = 'readout_audit'
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
    print('NEUMANN_PHYSICAL_CHARACTER_VERIFIER_SELF_TEST=PASS synthetic=1 rejected=' + str(len(bads)))


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
    print('NEUMANN_PHYSICAL_CHARACTER_COLD_EVIDENCE_VERIFIED')


if __name__ == '__main__':
    main()
