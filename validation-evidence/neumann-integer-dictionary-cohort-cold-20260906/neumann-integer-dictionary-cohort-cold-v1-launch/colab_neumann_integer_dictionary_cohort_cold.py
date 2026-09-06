#!/usr/bin/env python3
"""Fresh cold cohort for four physical counting and seven interval declarations.

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

SOURCE = 'af35fbb8c75bf2347543034b3abf27f0217b1bbf'
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
    runner.RUNNER_REV = 'neumann-integer-dictionary-cohort-cold-v1'
    runner.SOURCE_SHA = SOURCE
    base.SOURCE = SOURCE
    runner.ROOT = Path('/content/hrpoly-' + runner.RUNNER_REV)
    runner.EVIDENCE = Path(str(runner.ROOT) + '-evidence')
    runner.ARCHIVE = Path(str(runner.EVIDENCE) + '.tar.gz')
    runner.PATH_MANIFEST = Path(str(runner.ROOT) + '-paths.txt')
    runner.SOURCE_BLOBS = {
    "YangMills/RG/NeumannGeneratedIntegerCountingKernel.lean": "582ced7a01c70467916e2b515aac73655d23adcffe1b2e1596084845e6b1d691",
    "YangMills/RG/NeumannGeneratedIntegerCountingKernelAudit.lean": "425bad765720f435bef98f5c28dcbca5a1a548d3d166b37110ec89c6699ae184",
    "YangMills/RG/NeumannImageIntervalCoverage.lean": "65ec7c52bb48e094aec5486acabb4175bffd42838c07ae10e9e950fdd805daf0",
    "YangMills/RG/NeumannImageIntervalCoverageAudit.lean": "5b147b95ec02bd44491745485378382d69311bdb30a52a3be70628ad18008a48"
}
    audit_names = {
    "counting_audit": [
        "YangMills.RG.neumannFiniteSiteIntegerCoordinates_injective",
        "YangMills.RG.neumannGeneratedTerminalOwner_integerCoordinates",
        "YangMills.RG.neumannGeneratedTerminalOwner_eq_iff_integerCoordinates",
        "YangMills.RG.neumannGeneratedFlatCountingMass_integerOwner"
    ],
    "interval_audit": [
        "YangMills.RG.neumannOrbitFalse_periodQuotient",
        "YangMills.RG.neumannOrbitTrue_periodQuotient",
        "YangMills.RG.neumannOrbitFalse_periodRemainder",
        "YangMills.RG.neumannOrbitTrue_periodRemainder",
        "YangMills.RG.neumannImageIntervalFamily_injective",
        "YangMills.RG.neumannImageIntervalFamily_surjective",
        "YangMills.RG.neumannImageIntervalFamily_bijective"
    ]
}
    audit_names = {stage: frozenset(names) for stage, names in audit_names.items()}
    base.EXPECTED = frozenset().union(*audit_names.values())
    runner.QUEUE = [
        ("counting_focal", ["lake","build","YangMills.RG.NeumannGeneratedIntegerCountingKernel"], None),
        ("counting_audit", ["lake","env","lean","YangMills/RG/NeumannGeneratedIntegerCountingKernelAudit.lean"], audit_names["counting_audit"]),
        ("interval_focal", ["lake","build","YangMills.RG.NeumannImageIntervalCoverage"], None),
        ("interval_audit", ["lake","env","lean","YangMills/RG/NeumannImageIntervalCoverageAudit.lean"], audit_names["interval_audit"]),
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
        (runner.EVIDENCE / 'neumann-integer-dictionary-cohort-cold-contract.json').write_text(json.dumps({
            'source_sha': SOURCE,
            'parent_diagnostic_source': '99d0767ec84ed79e633556653bc2fe05047c79cf',
            'physical_diagnostic_source': 'eb2fde64ff5597e6c3fa49d3beb114633e806d37',
            'physical_diagnostic_archive_sha256': '91096b90e7d1583ee7b3ce88f3f09c2b74e2c882e618641df88efde17d43dbf9',
            'parent_diagnostic_archive_sha256': '34387a931f104302b88107f641ddac6741965b1ce18dad7f50486c28af55c1fc',
            'project_build_cache_restored': False,
            'durable_base_commit': BASE_SHA,
            'durable_base_sha256': '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892',
            'axiom_gate_sha256': '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
            'audit_expected': {stage: sorted(names) for stage, names in audit_names.items()},
            'queue': [stage for stage, _, _ in runner.QUEUE],
            'parser_self_test': {'accepted': 2, 'rejected': 9},
            'scope': 'finite physical counting-owner dictionary plus 1D full image-family bijection; not inverse, B0 or window15',
        }, sort_keys=True) + '\n', encoding='utf-8')
        outputs = {}
        for name in ["NeumannGeneratedIntegerCountingKernel.olean", "NeumannImageIntervalCoverage.olean"]:
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
