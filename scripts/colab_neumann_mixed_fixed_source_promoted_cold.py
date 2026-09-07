#!/usr/bin/env python3
"""Fresh cold gate for fixed-source injection and three declarations.

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

SOURCE = '8da9ffc57d7de329501fc5ba5d8084cdcbe5fb4f'
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
    runner.RUNNER_REV = 'neumann-mixed-fixed-source-promoted-cold-v1'
    runner.SOURCE_SHA = SOURCE
    base.SOURCE = SOURCE
    runner.ROOT = Path('/content/hrpoly-' + runner.RUNNER_REV)
    runner.EVIDENCE = Path(str(runner.ROOT) + '-evidence')
    runner.ARCHIVE = Path(str(runner.EVIDENCE) + '.tar.gz')
    runner.PATH_MANIFEST = Path(str(runner.ROOT) + '-paths.txt')
    runner.SOURCE_BLOBS = {
    "YangMills/RG/NeumannMixedFixedSource.lean": "ba89febbf4e1c2276c232627a59dec8052004c0398265b69e1866aaeb85dfaeb",
    "YangMills/RG/NeumannMixedFixedSourceAudit.lean": "2ac4868a1579ab62584124b7c325621252f57848aa4447a3cf0d297cb2473be3"
}
    audit_names = {
    "fixed_audit": [
        "YangMills.RG.neumannMixedInsertSource_injective",
        "YangMills.RG.neumannMixedFixedSourceImage_injective",
        "YangMills.RG.neumannMixedFixedSourceDifference_injective"
    ]
}
    audit_names = {stage: frozenset(names) for stage, names in audit_names.items()}
    base.EXPECTED = frozenset().union(*audit_names.values())
    runner.QUEUE = [
        ("fixed_focal", ["lake","build","YangMills.RG.NeumannMixedFixedSource"], None),
        ("fixed_audit", ["lake","env","lean","YangMills/RG/NeumannMixedFixedSourceAudit.lean"], audit_names["fixed_audit"]),
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
        (runner.EVIDENCE / 'neumann-mixed-fixed-source-promoted-cold-contract.json').write_text(json.dumps({
            'source_sha': SOURCE,
            'parent_diagnostics': [{"source":"ddbdd8913f91ff778594756bbecaad0d804dfb6c","archive_sha256":"85070e6d0aa48435546728425f1261863ce8130205fd1b6e1cba5e3585b1413f"}],
            'project_build_cache_restored': False,
            'durable_base_commit': BASE_SHA,
            'durable_base_sha256': '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892',
            'axiom_gate_sha256': '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
            'audit_expected': {stage: sorted(names) for stage, names in audit_names.items()},
            'queue': [stage for stage, _, _ in runner.QUEUE],
            'parser_self_test': {'accepted': 2, 'rejected': 9},
            'scope': 'fixed-source mixed image and difference injectivity; not full coverage at fixed source, physical carrier classification, physical inverse, uniform B0 or window15',
        }, sort_keys=True) + '\n', encoding='utf-8')
        outputs = {}
        for name in ["NeumannMixedFixedSource.olean"]:
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
