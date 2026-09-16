#!/usr/bin/env python3
"""Fresh cold gate for physical FULL classification and mixed summability.

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

SOURCE = '46bf719be34e586e83790fa1b2ff2092735faa12'
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
    runner.RUNNER_REV = 'neumann-physical-full-and-mixed-promoted-cold-v1'
    runner.SOURCE_SHA = SOURCE
    base.SOURCE = SOURCE
    runner.ROOT = Path('/content/hrpoly-' + runner.RUNNER_REV)
    runner.EVIDENCE = Path(str(runner.ROOT) + '-evidence')
    runner.ARCHIVE = Path(str(runner.EVIDENCE) + '.tar.gz')
    runner.PATH_MANIFEST = Path(str(runner.ROOT) + '-paths.txt')
    runner.SOURCE_BLOBS = {
    "YangMills/RG/NeumannPhysicalFullFlag.lean": "036df8c03dbfa206094cd8e321e862f0f614cf58be8b2f2511f7b07f45b1a6df",
    "YangMills/RG/NeumannPhysicalFullFlagAudit.lean": "314f540649b8ac1cd6e57238cfa6c7ace93faf7e3c33062dcb0ed7e74ca77e31",
    "YangMills/RG/NeumannPhysicalMixedSummability.lean": "64abbf07eee4773198d952c65563fcd7857d42da25befd80bb74e782a3352848",
    "YangMills/RG/NeumannPhysicalMixedSummabilityAudit.lean": "7ad480331727474991ce31ff9c0ea46b7b53e952110bd6ff2dea5a9ae3149a76"
}
    audit_names = {
    "full_audit": [
        "YangMills.RG.neumannPhysicalFullFlag_iff",
        "YangMills.RG.neumannPhysicalFullFlag_scale_test",
        "YangMills.RG.neumannPhysicalFullFlag_scale",
        "YangMills.RG.neumannPhysicalFullFlag_outgoing",
        "YangMills.RG.neumannPhysicalFullFlag_incoming"
    ],
    "mixed_audit": [
        "YangMills.RG.neumannMixedSourceDifference_injective",
        "YangMills.RG.summable_neumannMixedSource_of_decay",
        "YangMills.RG.summable_neumannActualFullGreen_mixedSource"
    ]
}
    audit_names = {stage: frozenset(names) for stage, names in audit_names.items()}
    base.EXPECTED = frozenset().union(*audit_names.values())
    runner.QUEUE = [
        ("physical_prerequisites", ["lake","build","YangMills.RG.NeumannRectangleDirectionalMasks","YangMills.RG.NeumannMixedOwnerTransport","YangMills.RG.NeumannPhysicalPeriodicSummability"], None),
        ("full_focal", ["lake","build","YangMills.RG.NeumannPhysicalFullFlag"], None),
        ("full_audit", ["lake","env","lean","YangMills/RG/NeumannPhysicalFullFlagAudit.lean"], audit_names["full_audit"]),
        ("mixed_focal", ["lake","build","YangMills.RG.NeumannPhysicalMixedSummability"], None),
        ("mixed_audit", ["lake","env","lean","YangMills/RG/NeumannPhysicalMixedSummabilityAudit.lean"], audit_names["mixed_audit"]),
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
        (runner.EVIDENCE / 'neumann-physical-full-and-mixed-promoted-cold-contract.json').write_text(json.dumps({
            'source_sha': SOURCE,
            'parent_diagnostics': [{"source":"f0c58431d20042ced9177632409e9f9bcbe79692","archive_sha256":"162921a7ec0141780ca1d0b3a9885ba6947451c8643574242341e27cb51ae32a","overlay_sha256":"e08cb291888b2627aa906a8f745d4ef44db5460f565823cd1de5df2baab3bf9a"},{"source":"bee3c451b41b5da2a1d876d7ad3f0de27a17bdee","archive_sha256":"77596ecfd1e2d699b0c2a06d7a9e242dce600d07f91257c39da00e86b83e3011","overlay_sha256":"b8b6ff9266521275039f54848a7bd50ccec00787ea9db3433f0b2e8d874bde90"}],
            'project_build_cache_restored': False,
            'durable_base_commit': BASE_SHA,
            'durable_base_sha256': '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892',
            'axiom_gate_sha256': '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
            'audit_expected': {stage: sorted(names) for stage, names in audit_names.items()},
            'queue': [stage for stage, _, _ in runner.QUEUE],
            'parser_self_test': {'accepted': 2, 'rejected': 9},
            'scope': 'actual mask FULL classification with fine/block scale transport, and literal full Green convergence on the same mixed index; not operator interchange, physical inverse, uniform B0 or window15',
        }, sort_keys=True) + '\n', encoding='utf-8')
        outputs = {}
        for name in ["NeumannPhysicalFullFlag.olean", "NeumannPhysicalMixedSummability.olean"]:
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

