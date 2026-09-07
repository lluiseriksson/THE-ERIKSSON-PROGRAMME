#!/usr/bin/env python3
"""Fresh cold gate for exact HOT selector/opposite production bodies.

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

SOURCE = '1885a6c0886e595f0d3013c6ac2b9a71f3c93036'
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
    runner.RUNNER_REV = 'neumann-selector-opposite-promoted-cold-v1'
    runner.SOURCE_SHA = SOURCE
    base.SOURCE = SOURCE
    runner.ROOT = Path('/content/hrpoly-' + runner.RUNNER_REV)
    runner.EVIDENCE = Path(str(runner.ROOT) + '-evidence')
    runner.ARCHIVE = Path(str(runner.EVIDENCE) + '.tar.gz')
    runner.PATH_MANIFEST = Path(str(runner.ROOT) + '-paths.txt')
    runner.SOURCE_BLOBS = {
    "YangMills/RG/NeumannAliasExponentialSelector.lean": "d1aa42857ed97359cfe381feea7dbde1d2762205eda3a1e043f2a22b9d38460c",
    "YangMills/RG/NeumannAliasExponentialSelectorAudit.lean": "2745d938c7f548587f441e8794ad3d67aa2e7a48d1c9811371a99fd5048575cb",
    "YangMills/RG/NeumannOppositeDifference.lean": "d2bd7b3e1c6d626770c87cbb85bc12b05a825e562a32d5afd78a414100fc7480",
    "YangMills/RG/NeumannOppositeDifferenceAudit.lean": "c5d848ab2f813ea83c08058d39b9027e62c27371171bba2a03ea488d208e6e1a"
}
    audit_names = {
    "selector_audit": [
        "YangMills.RG.neumannIntegerVectorCharacter_phase",
        "YangMills.RG.neumannCenteredAlias_exponential_sum",
        "YangMills.RG.neumannCenteredAlias_shiftedPhase_sum"
    ],
    "opposite_audit": [
        "YangMills.RG.neumannOppositeExponentialDifference",
        "YangMills.RG.neumannIntegerPlaneWave_centeredDifference"
    ]
}
    audit_names = {stage: frozenset(names) for stage, names in audit_names.items()}
    base.EXPECTED = frozenset().union(*audit_names.values())
    runner.QUEUE = [
        ("selector_focal", ["lake","build","YangMills.RG.NeumannAliasExponentialSelector"], None),
        ("selector_audit", ["lake","env","lean","YangMills/RG/NeumannAliasExponentialSelectorAudit.lean"], audit_names["selector_audit"]),
        ("opposite_focal", ["lake","build","YangMills.RG.NeumannOppositeDifference"], None),
        ("opposite_audit", ["lake","env","lean","YangMills/RG/NeumannOppositeDifferenceAudit.lean"], audit_names["opposite_audit"]),
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
        (runner.EVIDENCE / 'neumann-selector-opposite-promoted-cold-contract.json').write_text(json.dumps({
            'source_sha': SOURCE,
            'parent_diagnostics': [{"source":"0dcd87f8b60dfb464fb3a6707b8f65fe96637960","archive_sha256":"8b72d4250c6a2b8737dbbee6c719e647b7dd0377bc9174f48f9bbaad753c6d2c","source_blobs":{"tmp/NeumannAliasExponentialSelectorDraft.lean":"48777e553acc6f908a78bc3de7f04ad42068fd1d53a56a60f41449e2f15d2e01"}},{"source":"b3ca1ca8f749517014c934ff956116ecab19210d","archive_sha256":"026b3918979f14f7d3ca4f6e28135358e3ec58d76c1e7885973b0c32047972cb","source_blobs":{"tmp/NeumannOppositeDifferenceRepro.lean":"f0f97dee3b98e0410c69969d40aed56c45a2cc4be8d17db9c967d18d3d569864"}}],
            'project_build_cache_restored': False,
            'durable_base_commit': BASE_SHA,
            'durable_base_sha256': '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892',
            'axiom_gate_sha256': '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
            'audit_expected': {stage: sorted(names) for stage, names in audit_names.items()},
            'queue': [stage for stage, _, _ in runner.QUEUE],
            'parser_self_test': {'accepted': 2, 'rejected': 9},
            'scope': "finite alias exponential congruence selector and scalar opposite differences; not physical source equation, counting inverse, uniform B0 or window15",
        }, sort_keys=True) + '\n', encoding='utf-8')
        outputs = {}
        for name in ["NeumannAliasExponentialSelector.olean","NeumannOppositeDifference.olean"]:
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
