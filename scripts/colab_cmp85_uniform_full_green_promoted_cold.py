#!/usr/bin/env python3
"""Fresh cold gate for the promoted F4 scalar uniform-amplitude graph.

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

SOURCE = '5138e9bd4bc88797c91c21df5bb5c630c71600ca'
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
    runner.RUNNER_REV = 'cmp85-uniform-full-green-promoted-cold-v1'
    runner.SOURCE_SHA = SOURCE
    base.SOURCE = SOURCE
    runner.ROOT = Path('/content/hrpoly-' + runner.RUNNER_REV)
    runner.EVIDENCE = Path(str(runner.ROOT) + '-evidence')
    runner.ARCHIVE = Path(str(runner.EVIDENCE) + '.tar.gz')
    runner.PATH_MANIFEST = Path(str(runner.ROOT) + '-paths.txt')
    runner.SOURCE_BLOBS = {
        "YangMills/RG/BalabanCMP85SourceFullGreenUniformAmplitude.lean": "d6fa59d61117e6e37644c225026ce9b9eb77296ba734c3d73d3928aa36fe55a2",
        "YangMills/RG/BalabanCMP85SourceFullGreenHybridAmplitude.lean": "b091522c1d642cd476a08bcef6cdf8bdef04aabfc4e215da982a3d08ec04f796",
        "YangMills/RG/BalabanCMP85SourceFullGreenUniformAmplitudeAudit.lean": "6e307119e56d948694e3dd6844afb2e6209c30de5b892cdb7ea09a6e62452314",
        "YangMills/RG/BalabanCMP85SourceFullGreenHybridAmplitudeAudit.lean": "c04d26f5d824abd0b5027175debc8c00d54adaf8f66215e2e8fffa011b0a4218",
        "YangMills/RG/BalabanCMP85FullGreenNormalizedBudgetAudit.lean": "229c45bda97d544538a983c7eba2c10bcdeb9bc04fe725aee8c6a4ae2dbf3d00",
        "YangMills/RG/BalabanCMP85FullGreenNormalizedBudget.lean": "08ee61a8e184ccc107de1df62352339d852f5c906b786e1eed5c06c0cee38615"
    }
    audit_names = {
        "normalization_audit": [
            "YangMills.RG.CMP85FullGreenNormalizedBudget.split",
            "YangMills.RG.CMP85FullGreenNormalizedBudget.retain_inverse_square"
        ],
        "hybrid_audit": [
            "YangMills.RG.cmp85SourceFullGreen_fullBudget_le_hybrid"
        ],
        "uniform_audit": [
            "YangMills.RG.cmp85SourceFullGreenContourFactor_pos",
            "YangMills.RG.cmp85SourceFullGreenHybridAmplitudeConstant_nonneg",
            "YangMills.RG.cmp85SourceFullGreen_ownerAmplitude_split",
            "YangMills.RG.cmp85SourceFullGreen_ownerAmplitude_inverse_square",
            "YangMills.RG.exists_cmp85SourceFullGreen_uniformOwnerAmplitude"
        ]
    }
    audit_names = {stage: frozenset(names) for stage, names in audit_names.items()}
    base.EXPECTED = frozenset().union(*audit_names.values())
    runner.QUEUE = [
        ("normalization_focal", ["lake","build","YangMills.RG.BalabanCMP85FullGreenNormalizedBudget"], None),
        ("normalization_audit", ["lake","env","lean","YangMills/RG/BalabanCMP85FullGreenNormalizedBudgetAudit.lean"], audit_names["normalization_audit"]),
        ("hybrid_focal", ["lake","build","YangMills.RG.BalabanCMP85SourceFullGreenHybridAmplitude"], None),
        ("hybrid_audit", ["lake","env","lean","YangMills/RG/BalabanCMP85SourceFullGreenHybridAmplitudeAudit.lean"], audit_names["hybrid_audit"]),
        ("uniform_focal", ["lake","build","YangMills.RG.BalabanCMP85SourceFullGreenUniformAmplitude"], None),
        ("uniform_audit", ["lake","env","lean","YangMills/RG/BalabanCMP85SourceFullGreenUniformAmplitudeAudit.lean"], audit_names["uniform_audit"]),
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
        (runner.EVIDENCE / 'f4-uniform-cold-contract.json').write_text(json.dumps({
            'source_sha': SOURCE,
            'parent_diagnostic_source': 'be4e73409ac444d23e95c2eae2584fece5882f98',
            'parent_diagnostic_archive_sha256': '822844a908b0ea3a888ac1a03e9bb14908dfb6b24b53ae8f42eff0c793710eef',
            'project_build_cache_restored': False,
            'durable_base_commit': BASE_SHA,
            'durable_base_sha256': '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892',
            'axiom_gate_sha256': '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
            'audit_expected': {stage: sorted(names) for stage, names in audit_names.items()},
            'queue': [stage for stage, _, _ in runner.QUEUE],
            'parser_self_test': {'accepted': 2, 'rejected': 9},
            'scope': 'promoted F4 scalar full owner amplitude uniform in depth for fixed a,L; not regional/derivative B0 or window15',
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
