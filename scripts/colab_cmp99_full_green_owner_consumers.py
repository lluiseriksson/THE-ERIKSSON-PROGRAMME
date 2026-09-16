#!/usr/bin/env python3
"""Pinned, stop-on-first-error queue for PRE-VALIDATION steps 14 and 15.

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

SOURCE = 'ea524400bbf59777d461e8d04790516771258988'
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
    runner.RUNNER_REV = 'cmp99-full-green-owner-consumers-v2'
    runner.SOURCE_SHA = SOURCE
    base.SOURCE = SOURCE
    runner.ROOT = Path('/content/hrpoly-' + runner.RUNNER_REV)
    runner.EVIDENCE = Path(str(runner.ROOT) + '-evidence')
    runner.ARCHIVE = Path(str(runner.EVIDENCE) + '.tar.gz')
    runner.PATH_MANIFEST = Path(str(runner.ROOT) + '-paths.txt')
    runner.SOURCE_BLOBS = {
        'YangMills/RG/BalabanCMP99PhysicalFullGreenOwnerResidueBound.lean':
            '3b6ffeda9e55f8e43a9b1c480f91c4e521f883a0222659ba8fae903dad0ff03b',
        'YangMills/RG/BalabanCMP99PhysicalFullGreenOwnerResidueBoundAudit.lean':
            '2e11b1dd48db49e7d79d2a7ae969b240ab13c3836cfdadd1539fb87b75320c59',
        'YangMills/RG/BalabanCMP99GeneratedFullPointSourceOwnerBound.lean':
            'f56f4278f4dcaadcbe8cd87986e5acc5c92c3f019fd563c7e39879a826936049',
        'YangMills/RG/BalabanCMP99GeneratedFullPointSourceOwnerBoundAudit.lean':
            '03693386229db46bc711f70f853fb9c97d0fd221c2ec19417007cecd405d8101',
    }
    ns = 'YangMills.RG.'
    expected14 = frozenset(ns + x for x in (
        'cmp99PhysicalFullGreenUnscaledOwnerResidueSum',
        'cmp99PhysicalFullGreenOwnerResidue_affineBase_eq',
        'norm_cmp99PhysicalFullGreenUnscaledOwnerResidueSum_le_owner'))
    expected15 = frozenset(ns + x for x in (
        'cmp99PhysicalFullGreenOwnerAmplitude',
        'norm_cmp99SourceGeneratedFlatPhysicalPointSourceResidueClassSum_eq',
        'norm_cmp99SourceGeneratedFlatPhysicalPointSourceResidueClassSum_le_owner',
        'CMP99GeneratedFullPointSourceOwnerBoundCertificate.owner_bound',
        'cmp99GeneratedFullPointSourceOwnerBound'))
    base.EXPECTED = expected14 | expected15
    runner.QUEUE = [
        ('owner_residue_focal', ['lake', 'build',
            'YangMills.RG.BalabanCMP99PhysicalFullGreenOwnerResidueBound'], None),
        ('owner_residue_audit', ['lake', 'env', 'lean',
            'YangMills/RG/BalabanCMP99PhysicalFullGreenOwnerResidueBoundAudit.lean'], expected14),
        ('generated_owner_focal', ['lake', 'build',
            'YangMills.RG.BalabanCMP99GeneratedFullPointSourceOwnerBound'], None),
        ('generated_owner_audit', ['lake', 'env', 'lean',
            'YangMills/RG/BalabanCMP99GeneratedFullPointSourceOwnerBoundAudit.lean'], expected15),
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
            'parent_cold_seal': '88d7ccc77abaee3d75b1eb06a4f233e31d7a5591',
            'durable_base_commit': BASE_SHA,
            'durable_base_sha256': '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892',
            'axiom_gate_sha256': '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
            'audit_expected': {'owner_residue_audit': sorted(expected14),
                               'generated_owner_audit': sorted(expected15)},
            'queue': [stage for stage, _, _ in runner.QUEUE],
            'parser_self_test': {'accepted': 2, 'rejected': 9},
            'scope': 'fixed-coefficient owner bounds; not uniform B0 or window15',
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
