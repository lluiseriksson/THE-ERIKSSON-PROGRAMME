#!/usr/bin/env python3
"""Fresh cold gate for normalized Haar and exact centered-alias characters.

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

SOURCE = '98f4337e06271a7d5e3957450440292db0f79168'
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
    runner.RUNNER_REV = 'neumann-character-normalization-promoted-cold-v1'
    runner.SOURCE_SHA = SOURCE
    base.SOURCE = SOURCE
    runner.ROOT = Path('/content/hrpoly-' + runner.RUNNER_REV)
    runner.EVIDENCE = Path(str(runner.ROOT) + '-evidence')
    runner.ARCHIVE = Path(str(runner.EVIDENCE) + '.tar.gz')
    runner.PATH_MANIFEST = Path(str(runner.ROOT) + '-paths.txt')
    runner.SOURCE_BLOBS = {
    "YangMills/RG/NeumannTorusCharacterIntegral.lean": "20d7bc9af233cf277d8dd4154259c1e720d8c53242d85648be07de9062ed4bed",
    "YangMills/RG/NeumannTorusCharacterIntegralAudit.lean": "8835e6b90a9e80a193843d078dd093d11226114c168fb7341e539a440a5174c1",
    "YangMills/RG/NeumannCenteredAliasCharacter.lean": "f73793ea7a03f17a7a9bf32174ce3da63312e908c2cfd2e052df6c9ce45cbce3",
    "YangMills/RG/NeumannCenteredAliasCharacterAudit.lean": "958aa940e976db73369aaf4737cc9a79d3324e95e3af716cdd4ac4484b5d534c"
}
    audit_names = {
    "haar_audit": [
        "YangMills.RG.neumannUnitCircle_volume_eq_normalizedHaar",
        "YangMills.RG.neumannTorus_normalizedCharacterIntegral"
    ],
    "alias_audit": [
        "YangMills.RG.neumannCenteredAliasVectorResidueEquiv_apply",
        "YangMills.RG.neumannCenteredAlias_character_sum",
        "YangMills.RG.neumannIntegerCharacter_product_phase"
    ]
}
    audit_names = {stage: frozenset(names) for stage, names in audit_names.items()}
    base.EXPECTED = frozenset().union(*audit_names.values())
    runner.QUEUE = [
        ("haar_focal", ["lake","build","YangMills.RG.NeumannTorusCharacterIntegral"], None),
        ("haar_audit", ["lake","env","lean","YangMills/RG/NeumannTorusCharacterIntegralAudit.lean"], audit_names["haar_audit"]),
        ("alias_prerequisites", ["lake","build","YangMills.RG.BalabanCMP99SourceCenteredAliasReflection","YangMills.RG.BalabanCMP99FlatMultidimensionalDFT"], None),
        ("alias_focal", ["lake","build","YangMills.RG.NeumannCenteredAliasCharacter"], None),
        ("alias_audit", ["lake","env","lean","YangMills/RG/NeumannCenteredAliasCharacterAudit.lean"], audit_names["alias_audit"]),
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
        (runner.EVIDENCE / 'neumann-character-normalization-promoted-cold-contract.json').write_text(json.dumps({
            'source_sha': SOURCE,
            'parent_diagnostics': [{"source":"a5811d5ddd78faf6fe638aa00db30276af826baf","archive_sha256":"d80bf1b479adfafb568d43335c229c98b060aab77b7d26cadfbabbed5c9e83de","source_blobs":{"tmp/NeumannTorusCharacterIntegralRepro.lean":"78e060fc4b296ca2aa14b79281850e6f0921fd17df183f24b809d18754c64317","tmp/NeumannCenteredAliasCharacterDraft.lean":"33e22d4852cbdf17f2d44445528fef1afbd2106f9b63c74d6ca10c867a926b53"}}],
            'project_build_cache_restored': False,
            'durable_base_commit': BASE_SHA,
            'durable_base_sha256': '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892',
            'axiom_gate_sha256': '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
            'audit_expected': {stage: sorted(names) for stage, names in audit_names.items()},
            'queue': [stage for stage, _, _ in runner.QUEUE],
            'parser_self_test': {'accepted': 2, 'rejected': 9},
            'scope': "normalized Haar character integral and literal centered-alias character identities; not physical source equation, regional inverse, uniform B0 or window15",
        }, sort_keys=True) + '\n', encoding='utf-8')
        outputs = {}
        for name in ["NeumannTorusCharacterIntegral.olean", "NeumannCenteredAliasCharacter.olean"]:
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
