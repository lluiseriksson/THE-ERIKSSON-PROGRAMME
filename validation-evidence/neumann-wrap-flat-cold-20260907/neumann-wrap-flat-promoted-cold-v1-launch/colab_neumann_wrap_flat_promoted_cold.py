#!/usr/bin/env python3
"""Fresh cold gate for the three wrap/flat Neumann declarations.

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

SOURCE = '15e776db59c051571f79e47974acc2fbf597f715'
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
    runner.RUNNER_REV = 'neumann-wrap-flat-promoted-cold-v1'
    runner.SOURCE_SHA = SOURCE
    base.SOURCE = SOURCE
    runner.ROOT = Path('/content/hrpoly-' + runner.RUNNER_REV)
    runner.EVIDENCE = Path(str(runner.ROOT) + '-evidence')
    runner.ARCHIVE = Path(str(runner.EVIDENCE) + '.tar.gz')
    runner.PATH_MANIFEST = Path(str(runner.ROOT) + '-paths.txt')
    runner.SOURCE_BLOBS = {
    "YangMills/RG/NeumannRectangleWrapProbe.lean": "8b40976b50f7941c6a0f28cf51b6c6de63b9df88135e1cd38f99487128a6ec27",
    "YangMills/RG/NeumannRectangleWrapProbeAudit.lean": "0b92a2ebe22727f5a820817e2586d6317c4ec77a07a9ffcd88d7cac8662e07c1",
    "YangMills/RG/NeumannFlatInternalBondAction.lean": "3a2322b9877003a82dff5eb5c04122d6702eba1a7fb789d3bfbe954e55a948d4",
    "YangMills/RG/NeumannFlatInternalBondActionAudit.lean": "a4fdfac46689b4e3dffe40ecd35cea54bb54bfe93f802ad30a5e47b1e9101a76"
}
    audit_names = {
    "wrap_probe_audit": [
        "YangMills.RG.neumannRectangle_siteFit_retains_wrapBond"
    ],
    "flat_action_audit": [
        "YangMills.RG.neumannFlatInternalBond_extendedDerivative_apply",
        "YangMills.RG.neumannFlatInternalBond_laplacian_apply"
    ]
}
    audit_names = {stage: frozenset(names) for stage, names in audit_names.items()}
    base.EXPECTED = frozenset().union(*audit_names.values())
    runner.QUEUE = [
        ("wrap_probe_focal", ["lake","build","YangMills.RG.NeumannRectangleWrapProbe"], None),
        ("wrap_probe_audit", ["lake","env","lean","YangMills/RG/NeumannRectangleWrapProbeAudit.lean"], audit_names["wrap_probe_audit"]),
        ("flat_action_focal", ["lake","build","YangMills.RG.NeumannFlatInternalBondAction"], None),
        ("flat_action_audit", ["lake","env","lean","YangMills/RG/NeumannFlatInternalBondActionAudit.lean"], audit_names["flat_action_audit"]),
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
        (runner.EVIDENCE / 'neumann-wrap-flat-promoted-cold-contract.json').write_text(json.dumps({
            'source_sha': SOURCE,
            'parent_diagnostics': [{"source":"baf5fa136663fe71a9cf07dacd4e365b0026942e","archive_sha256":"0f9875ee8fdb56e62df2cb0281c67b1b675876828cda7b359582cc60c14b391d"},{"source":"69a5308c8e5635b95b59c6d5c88d4b5b789f851c","archive_sha256":"0e7af449f57a9390481ae3384944561f8ff215c23cdb273cc4525982eee6c427"}],
            'project_build_cache_restored': False,
            'durable_base_commit': BASE_SHA,
            'durable_base_sha256': '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892',
            'axiom_gate_sha256': '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
            'audit_expected': {stage: sorted(names) for stage, names in audit_names.items()},
            'queue': [stage for stage, _, _ in runner.QUEUE],
            'parser_self_test': {'accepted': 2, 'rejected': 9},
            'scope': 'actual torus wrap witness and flat internal-bond derivative/Laplacian only; not integer boundary identification, regional inverse, uniform B0 or window15',
        }, sort_keys=True) + '\n', encoding='utf-8')
        outputs = {}
        for name in ["NeumannRectangleWrapProbe.olean","NeumannFlatInternalBondAction.olean"]:
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
