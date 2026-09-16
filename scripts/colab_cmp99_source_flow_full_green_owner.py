#!/usr/bin/env python3
"""Pinned, stop-on-first-error queue for PRE-VALIDATION generic F2 and source-flow F3.

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

SOURCE = 'bab82db79c118ef64259bc50627170f11c2e187e'
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
    runner.RUNNER_REV = 'cmp99-source-flow-full-green-owner-v1'
    runner.SOURCE_SHA = SOURCE
    base.SOURCE = SOURCE
    runner.ROOT = Path('/content/hrpoly-' + runner.RUNNER_REV)
    runner.EVIDENCE = Path(str(runner.ROOT) + '-evidence')
    runner.ARCHIVE = Path(str(runner.EVIDENCE) + '.tar.gz')
    runner.PATH_MANIFEST = Path(str(runner.ROOT) + '-paths.txt')
    runner.SOURCE_BLOBS = {
        "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceOwnerResidueIdentity.lean": "a6c552d832c83c0d2a230eb4257b57a5b175c0313c554c9de304cd9987cbd99a",
        "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceOwnerResidueIdentityAudit.lean": "098b3a5062bec4de77f1e73953cae83964c6c6ba3832f0716a41b6e60003f343",
        "YangMills/RG/BalabanCMP99SourceFlowFullPointSourceOwnerBound.lean": "e730e8567ea491d0f8a2f6070edc156bf20edbe7b5d03b445765a342d0af3cc5",
        "YangMills/RG/BalabanCMP99SourceFlowFullPointSourceOwnerBoundAudit.lean": "d549840102e22fab621e75494f519631c03402fe0a855eabbdfdf84155262935"
    }
    ns = 'YangMills.RG.'
    expected14 = frozenset({ns + 'cmp99SourceFlatFullPointSourceSolution_eq_scaledOwnerResidue'})
    expected15 = frozenset(ns + x for x in (
        'norm_cmp99PhysicalFullGreenScaledOwnerResidue_le_owner',
        'cmp99SourceFlowFullPointSourceGreen_apply_eq_scaledOwnerResidue',
        'norm_cmp99SourceFlowFullPointSourceGreen_le_owner'))
    base.EXPECTED = expected14 | expected15
    runner.QUEUE = [
        ('generic_residue_focal', ['lake', 'build',
            'YangMills.RG.BalabanCMP99SourceFlatFullPointSourceOwnerResidueIdentity'], None),
        ('generic_residue_audit', ['lake', 'env', 'lean',
            'YangMills/RG/BalabanCMP99SourceFlatFullPointSourceOwnerResidueIdentityAudit.lean'], expected14),
        ('source_owner_focal', ['lake', 'build',
            'YangMills.RG.BalabanCMP99SourceFlowFullPointSourceOwnerBound'], None),
        ('source_owner_audit', ['lake', 'env', 'lean',
            'YangMills/RG/BalabanCMP99SourceFlowFullPointSourceOwnerBoundAudit.lean'], expected15),
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
            'parent_cold_seal': 'cd01194884a8bab97518a09ba9caa0bf8be84e35',
            'durable_base_commit': BASE_SHA,
            'durable_base_sha256': '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892',
            'axiom_gate_sha256': '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
            'audit_expected': {'generic_residue_audit': sorted(expected14),
                               'source_owner_audit': sorted(expected15)},
            'queue': [stage for stage, _, _ in runner.QUEUE],
            'parser_self_test': {'accepted': 2, 'rejected': 9},
            'scope': 'generic full point-source residue identity and literal source-flow owner bound; not uniform B0 or window15',
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
