#!/usr/bin/env python3
"""Pinned, stop-on-first-error queue for PRE-VALIDATION source-flow F1 and scalar foundations.

Fresh Colab CPU/high-RAM checkout; no restored project build. Focal/audit
evidence only: not a root build, uniform B0 or a terminal hRpoly result.
The completed runtime is retained only long enough to preserve evidence.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import types
import urllib.request

SOURCE = '098cf3dfad1095c57bdc1d1dc5bc6b13252174d5'
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
    runner.RUNNER_REV = 'cmp99-source-flow-full-green-foundations-v1'
    runner.SOURCE_SHA = SOURCE
    base.SOURCE = SOURCE
    runner.ROOT = Path('/content/hrpoly-' + runner.RUNNER_REV)
    runner.EVIDENCE = Path(str(runner.ROOT) + '-evidence')
    runner.ARCHIVE = Path(str(runner.EVIDENCE) + '.tar.gz')
    runner.PATH_MANIFEST = Path(str(runner.ROOT) + '-paths.txt')
    runner.SOURCE_BLOBS = {
        "YangMills/RG/BalabanCMP85SourceFullGreenScalarFoundations.lean": "a89a913f6ac7c0a926e2a81c8c084583a58166ce0a72944d97831ecd20ef5809",
        "YangMills/RG/BalabanCMP85SourceFullGreenScalarFoundationsAudit.lean": "9ddd5a3afe6af578f89eab61b5c56ee2106cbe48c75f0ca89af326ec685aebe7",
        "YangMills/RG/BalabanCMP99SourceFlowFullPointSourceGreenIdentification.lean": "096f3be452787a7703de26cec90a16526f488da3f7b0327b6f5422ff31ebefac",
        "YangMills/RG/BalabanCMP99SourceFlowFullPointSourceGreenIdentificationAudit.lean": "af3f129c7eaaf0ca1c8593fcbd36deff68c294e0dac98d04733f1c0b59c20845"
    }
    ns = 'YangMills.RG.'
    expected14 = frozenset(ns + x for x in (
        'cmp85SourceFullGreen_massParameter_le_initial',
        'cmp85SourceFullGreen_momentBudget_eq_scalarAmplitude',
        'cmp85SourceFullGreen_momentBudget_antitone',
        'exists_cmp85SourceFullGreen_uniformRadiusAndMoment'))
    expected15 = frozenset({ns + 'cmp99SourceFlowFullPointSourceSolution_eq_green_apply'})
    base.EXPECTED = expected14 | expected15
    runner.QUEUE = [
        ('source_scalar_focal', ['lake', 'build',
            'YangMills.RG.BalabanCMP85SourceFullGreenScalarFoundations'], None),
        ('source_scalar_audit', ['lake', 'env', 'lean',
            'YangMills/RG/BalabanCMP85SourceFullGreenScalarFoundationsAudit.lean'], expected14),
        ('source_inverse_focal', ['lake', 'build',
            'YangMills.RG.BalabanCMP99SourceFlowFullPointSourceGreenIdentification'], None),
        ('source_inverse_audit', ['lake', 'env', 'lean',
            'YangMills/RG/BalabanCMP99SourceFlowFullPointSourceGreenIdentificationAudit.lean'], expected15),
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
        (runner.EVIDENCE / 'owner-queue-contract.json').write_text(json.dumps({
            'source_sha': SOURCE,
            'parent_cold_seal': 'bfa7b030618e26ee93312460778c9ca23fefbe83',
            'durable_base_commit': BASE_SHA,
            'durable_base_sha256': '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892',
            'axiom_gate_sha256': '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
            'audit_expected': {'source_scalar_audit': sorted(expected14),
                               'source_inverse_audit': sorted(expected15)},
            'queue': [stage for stage, _, _ in runner.QUEUE],
            'parser_self_test': {'accepted': 2, 'rejected': 9},
            'scope': 'source-flow full inverse identity and scalar windows; not uniform full B0 or window15',
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
