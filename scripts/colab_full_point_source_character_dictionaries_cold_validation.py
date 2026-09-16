#!/usr/bin/env python3
"""Cold Colab seal for the four reflected full-G point-source dictionaries."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import re
import urllib.request


PARENT_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "d5946c390cd39df9c9a74ccca6fdaa6fd553e988/"
    "scripts/colab_cmp89_mass_uniform_cold_validation.py"
)
PARENT_SHA256 = "baec81104da84649159e30298ad7b547096e00bff362776e347386657014158a"
PARENT = Path("/content/colab_cmp89_mass_uniform_cold_validation.py")

with urllib.request.urlopen(PARENT_URL, timeout=60) as response:
    parent_source = response.read()
parent_hash = hashlib.sha256(parent_source).hexdigest()
print("PARENT_RUNNER_TRANSPORT_SHA256=" + parent_hash, flush=True)
if parent_hash != PARENT_SHA256:
    raise RuntimeError("PARENT_RUNNER_TRANSPORT_HASH_MISMATCH")
PARENT.write_bytes(parent_source)
spec = importlib.util.spec_from_file_location("full_point_source_dictionary_parent", PARENT)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load parent runner: {PARENT}")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)
runner = parent.runner


EXPECTED = {
    501: {
        "YangMills.RG.cmp99FlatFourierMode_inv_eq_finePointSourceAliasVector_mul_coarseMode_inv",
        "YangMills.RG.cmp99FlatFourierMode_inv_eq_owned_finePointSourceAliasVector_mul_coarseMode_inv",
        "YangMills.RG.cmp89Eq246FinePointSourceAliasVector_comp_reflection_eq_neg",
        "YangMills.RG.cmp99SourceFlatFullComplexPrecisionPointSourceFibreCoefficients_apply_eq",
    },
    502: {
        "YangMills.RG.cmp99FlatFourierMode_eq_fineTargetAliasPhase_mul_coarseMode",
        "YangMills.RG.cmp99FlatFourierMode_eq_owned_fineTargetAliasPhase_mul_coarseMode",
    },
    503: {
        "YangMills.RG.cmp99SourceFlatFullComplexPrecisionPointSourceFibreSolution_apply_eq_integrand",
    },
    504: {
        "YangMills.RG.cmp99SourceFlatFullComplexPrecisionPointSourceSolution_apply_eq_outerIntegrandSum",
    },
}


def parse_axioms_exact(output: str, expected_key: int) -> None:
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool", "Lean.ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    with_axioms = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact)
    without_axioms = re.findall(r"'([^']+)'doesnotdependonanyaxioms", compact)
    names = {name for name, _ in with_axioms} | set(without_axioms)
    expected_names = EXPECTED.get(expected_key)
    if expected_names is None:
        raise RuntimeError("UNEXPECTED_AXIOM_GATE_KEY=" + str(expected_key))
    if len(with_axioms) + len(without_axioms) != len(expected_names):
        raise RuntimeError("AXIOM_BLOCK_COUNT_MISMATCH=" + repr((with_axioms, without_axioms)))
    if names != expected_names:
        raise RuntimeError("AXIOM_DECLARATION_MISMATCH=" + repr(sorted(names)))
    for name, raw_axioms in with_axioms:
        axioms = {item for item in raw_axioms.split(",") if item}
        if not axioms.issubset(runner.ALLOWED_AXIOMS):
            raise RuntimeError("AXIOM_SET=" + name + ":" + repr(sorted(axioms)))
        print("AXIOM_GATE=" + name + " AXIOMS=" + ",".join(sorted(axioms)), flush=True)
    for name in without_axioms:
        print("AXIOM_GATE=" + name + " AXIOMS=", flush=True)


runner.parse_axioms = parse_axioms_exact
runner.RUNNER_REV = "full-point-source-character-dictionaries-cold-v1"
runner.SOURCE_SHA = "ea72912edf9fd40121589ed89854a9bc9ebf02bb"
runner.MIN_RAM_GIB = 11.0
runner.ALLOW_GPU_RUNTIME = False
runner.ROOT = Path("/content/hrpoly-full-point-source-dictionaries-cold-v1")
runner.EVIDENCE = Path("/content/hrpoly-full-point-source-dictionaries-cold-v1-evidence")
runner.ARCHIVE = Path("/content/hrpoly-full-point-source-dictionaries-cold-v1-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-full-point-source-dictionaries-cold-v1-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceCharacterDictionary.lean": "699c735fb9025cd19178f79f547466fb8633fb399576f7bbcdcfd281eec88799",
    "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceCharacterDictionaryAudit.lean": "e57f9e3be269811e50a9983dfe421527379fe6b3be48a0e0f4c36adc261746bf",
    "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceTargetCharacterDictionary.lean": "3d2452dd2b9bbdac44adf229320f90fff9083d5e5c5a0af8109f5d66907fcc2e",
    "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceTargetCharacterDictionaryAudit.lean": "ead7abc4299489927ef24fc75ebb5d6df9db455161096ec43f28578409fa92e7",
    "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceFibreIntegrandDictionary.lean": "882333f48bb72956c23fe1ee6291dd097769722d195d42de87f45c4f9045d7ec",
    "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceFibreIntegrandDictionaryAudit.lean": "b6b1fc6aa2bd557f6a027e3e46ca8b32f266af8878fff37aa04cd7bc5e628a29",
    "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceOuterSynthesisDictionary.lean": "340d6a8e0af6fbb371954ab12b2dcebaabaa656f979de935c3fe2ff0da58bf80",
    "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceOuterSynthesisDictionaryAudit.lean": "cabeacdc5319f6d3a1d9a903656d1ae90bab1da759c53f71765f04aeef980123",
}
runner.QUEUE = [
    ("source_character_focal", ["lake", "build", "YangMills.RG.BalabanCMP99SourceFlatFullPointSourceCharacterDictionary"], None),
    ("source_character_audit", ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceCharacterDictionaryAudit.lean"], 501),
    ("target_character_focal", ["lake", "build", "YangMills.RG.BalabanCMP99SourceFlatFullPointSourceTargetCharacterDictionary"], None),
    ("target_character_audit", ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceTargetCharacterDictionaryAudit.lean"], 502),
    ("fibre_integrand_focal", ["lake", "build", "YangMills.RG.BalabanCMP99SourceFlatFullPointSourceFibreIntegrandDictionary"], None),
    ("fibre_integrand_audit", ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceFibreIntegrandDictionaryAudit.lean"], 503),
    ("outer_synthesis_focal", ["lake", "build", "YangMills.RG.BalabanCMP99SourceFlatFullPointSourceOuterSynthesisDictionary"], None),
    ("outer_synthesis_audit", ["lake", "env", "lean", "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceOuterSynthesisDictionaryAudit.lean"], 504),
]


if __name__ == "__main__":
    saved_unassign = None
    try:
        from google.colab import runtime

        saved_unassign = runtime.unassign
        runtime.unassign = lambda: print("RUNTIME_RETAINED_FOR_EVIDENCE=1", flush=True)
    except ImportError:
        pass
    try:
        raise SystemExit(runner.main())
    finally:
        if saved_unassign is not None:
            from google.colab import runtime

            runtime.unassign = saved_unassign
