#!/usr/bin/env python3
"""Fresh cold gate for masked differences and literal physical characters/readout.

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

SOURCE = '29a48ac4bb1058cd71b74f65029e918d49e74b60'
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
    runner.RUNNER_REV = 'neumann-physical-character-promoted-cold-v1'
    runner.SOURCE_SHA = SOURCE
    base.SOURCE = SOURCE
    runner.ROOT = Path('/content/hrpoly-' + runner.RUNNER_REV)
    runner.EVIDENCE = Path(str(runner.ROOT) + '-evidence')
    runner.ARCHIVE = Path(str(runner.EVIDENCE) + '.tar.gz')
    runner.PATH_MANIFEST = Path(str(runner.ROOT) + '-paths.txt')
    runner.SOURCE_BLOBS = {
    "YangMills/RG/NeumannAliasPrecisionReadout.lean": "216c2218483217be2ea18cfba1e9567246d051776f5080acf718fedee51e0a85",
    "YangMills/RG/NeumannAliasPrecisionReadoutAudit.lean": "ce59a432bfdc298ad804eb8ed2329892ac10f7e43a5b88a71918f3e6766a1e95",
    "YangMills/RG/NeumannMaskedDifference.lean": "976c3f090fd8d5f0e73c11d40f65956f30b5b0bba500ecd0c795ca822a505c45",
    "YangMills/RG/NeumannMaskedDifferenceAudit.lean": "600aa41bcfc8915cdb894d63b699ef20e1e041da7afa60689d88b58b10b16b62",
    "YangMills/RG/NeumannPhysicalBrillouinCharacter.lean": "a065cba1db9858fb9b34f53183026dc3fd39db07f41153c36a770764a3151c84",
    "YangMills/RG/NeumannPhysicalBrillouinCharacterAudit.lean": "52242ac12b71238d916729072871802710f04c36d20593ed327afa7ca2afa57f"
}
    audit_names = {
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
    audit_names = {stage: frozenset(names) for stage, names in audit_names.items()}
    base.EXPECTED = frozenset().union(*audit_names.values())
    runner.QUEUE = [
        ("mask_focal", ["lake","build","YangMills.RG.NeumannMaskedDifference"], None),
        ("mask_audit", ["lake","env","lean","YangMills/RG/NeumannMaskedDifferenceAudit.lean"], audit_names["mask_audit"]),
        ("physical_focal", ["lake","build","YangMills.RG.NeumannPhysicalBrillouinCharacter"], None),
        ("physical_audit", ["lake","env","lean","YangMills/RG/NeumannPhysicalBrillouinCharacterAudit.lean"], audit_names["physical_audit"]),
        ("readout_focal", ["lake","build","YangMills.RG.NeumannAliasPrecisionReadout"], None),
        ("readout_audit", ["lake","env","lean","YangMills/RG/NeumannAliasPrecisionReadoutAudit.lean"], audit_names["readout_audit"]),
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
        (runner.EVIDENCE / 'neumann-physical-character-promoted-cold-contract.json').write_text(json.dumps({
            'source_sha': SOURCE,
            'parent_diagnostics': [{"source":"98f4337e06271a7d5e3957450440292db0f79168","archive_sha256":"2b8c8aa39332e863f79a90fbbcdaaa559caa4ce8108cb027353d7e04e6ad4780","source_blobs":{"tmp/NeumannMaskedDifferenceRepro.lean":"70903fca9cf0e0510bf300f8e77b01d97da5bcd2d1b165adce98cea037814b09"}},{"source":"ce9cc5cc858214ee4e80fca27e6854d22567f653","archive_sha256":"a6618a294b75d5437093bc859f802273889fa9170f092395dc2d1e5156dac3e1","source_blobs":{"tmp/NeumannPhysicalBrillouinCharacterDraft.lean":"c845da5c7961927047d0e8974031d2ff29c7791d7be8bb6113c99f16dc44dc75","tmp/NeumannAliasPrecisionReadoutDraft.lean":"ddcc7a677396a175bea22e002304b00fe4c9b89de52f2714605eb59b3f5e2274"}}],
            'project_build_cache_restored': False,
            'durable_base_commit': BASE_SHA,
            'durable_base_sha256': '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892',
            'axiom_gate_sha256': '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
            'audit_expected': {stage: sorted(names) for stage, names in audit_names.items()},
            'queue': [stage for stage, _, _ in runner.QUEUE],
            'parser_self_test': {'accepted': 2, 'rejected': 9},
            'scope': "masked endpoint differences, literal physical character integral and alias precision readout; not actual finite operator action, counting inverse, uniform B0 or window15",
        }, sort_keys=True) + '\n', encoding='utf-8')
        outputs = {}
        for name in ["NeumannMaskedDifference.olean","NeumannPhysicalBrillouinCharacter.olean","NeumannAliasPrecisionReadout.olean"]:
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
