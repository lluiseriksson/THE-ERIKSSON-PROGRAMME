#!/usr/bin/env python3
"""Colab debug gate for the finite CMP89 physical right-inverse interface."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import re
import urllib.request


HERE = Path("/content")
BASE_RUNNER = HERE / "colab_qprime_row_validation.py"
BASE_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "bcc852cee5e709bff91fad7de26fa21cff754e1f/"
    "scripts/colab_qprime_row_validation.py"
)
BASE_RUNNER_SHA256 = (
    "d06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee"
)
with urllib.request.urlopen(BASE_RUNNER_URL) as response:
    base_runner_source = response.read()
base_runner_hash = hashlib.sha256(base_runner_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + base_runner_hash, flush=True)
if base_runner_hash != BASE_RUNNER_SHA256:
    raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
BASE_RUNNER.write_bytes(base_runner_source)
spec = importlib.util.spec_from_file_location(
    "cmp89_physical_neumann_inverse_producer_base", BASE_RUNNER
)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED_POINT_SOURCE_DECLARATIONS = {
    "YangMills.RG.finitePiLp_comp_eq_id_iff_pointSources",
}

EXPECTED_MASS_DECLARATIONS = {
    "YangMills.RG.mass_sq_mul_cmp89NeumannReflectionSeries",
    "YangMills.RG.mass_sq_comp_cmp89NeumannScalarReflectionOperator",
}

EXPECTED_THREE_SPECIES_DECLARATIONS = {
    "YangMills.RG.cmp89SourceNeumannRegionalGaugePrecision_eq_threeSpecies",
    "YangMills.RG.cmp89SourceNeumannRegionalGaugePrecision_comp_eq_threeSpecies",
}

EXPECTED_PHYSICAL_DECLARATIONS = {
    "YangMills.RG.cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalSpacing",
    "YangMills.RG.cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannFourierCoefficient",
    "YangMills.RG.cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannTerminalSpacing_eq_one",
    "YangMills.RG.cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannFourierCoefficient_eq_prefixA",
    "YangMills.RG.cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalFullGreen",
    "YangMills.RG.CMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalRightInverse",
    "YangMills.RG.cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalRepresentation_of_rightInverse",
}

EXPECTED_DECLARATION_SETS = (
    EXPECTED_POINT_SOURCE_DECLARATIONS,
    EXPECTED_MASS_DECLARATIONS,
    EXPECTED_THREE_SPECIES_DECLARATIONS,
    EXPECTED_PHYSICAL_DECLARATIONS,
)


def parse_axioms_exact(output: str, expected: int) -> None:
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool", "Lean.ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    with_axioms = re.findall(
        r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact
    )
    without_axioms = re.findall(
        r"'([^']+)'doesnotdependonanyaxioms", compact
    )
    names = {name for name, _ in with_axioms} | set(without_axioms)
    if len(with_axioms) + len(without_axioms) != expected:
        raise RuntimeError(
            "AXIOM_BLOCK_COUNT_MISMATCH="
            + repr((with_axioms, without_axioms))
        )
    matching_declaration_sets = [
        declarations
        for declarations in EXPECTED_DECLARATION_SETS
        if len(declarations) == expected and names == declarations
    ]
    if len(matching_declaration_sets) != 1:
        raise RuntimeError("AXIOM_DECLARATION_MISMATCH=" + repr(sorted(names)))
    for name, raw_axioms in with_axioms:
        axioms = {item for item in raw_axioms.split(",") if item}
        if not axioms.issubset(runner.ALLOWED_AXIOMS):
            raise RuntimeError("AXIOM_SET=" + name + ":" + repr(sorted(axioms)))
        print(
            "AXIOM_GATE=" + name + " AXIOMS=" + ",".join(sorted(axioms)),
            flush=True,
        )
    for name in without_axioms:
        print("AXIOM_GATE=" + name + " AXIOMS=", flush=True)


runner.parse_axioms = parse_axioms_exact
runner.RUNNER_REV = "cmp89-physical-neumann-inverse-producer-debug-v5"
runner.SOURCE_SHA = "27cb70c3e4a8dd556aea65343c599d1e5df8d708"
runner.ROOT = Path("/content/hrpoly-cmp89-physical-neumann-inverse-producer-debug-v5")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp89-physical-neumann-inverse-producer-debug-v5-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp89-physical-neumann-inverse-producer-debug-v5-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp89-physical-neumann-inverse-producer-debug-v5-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89NeumannMassReflection.lean":
        "a5e5f55e7b5cc5f0a8580b9de05c3c3c3ce0fb5b126abdfc5c94ae21d1c9753f",
    "YangMills/RG/BalabanCMP89NeumannMassReflectionAudit.lean":
        "497467b74e145744482674dc59b5138661d37c7ec565675fe7c8909b87d9c095",
    "YangMills/RG/BalabanCMP89NeumannPrecisionThreeSpecies.lean":
        "282a68fb3f578d739f4a6ac8d659f16debd57f2b3377f90c9fb1bf55ec754074",
    "YangMills/RG/BalabanCMP89NeumannPrecisionThreeSpeciesAudit.lean":
        "4404349c64655597ec26bffe759d114671fd9a0a8fdcc710682bdfa2009073e1",
    "YangMills/RG/BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectanglePhysicalInverseProducer.lean":
        "920f03c5e4c811d7f59c2b64fa4c50b41347a3b957aad72e72701e98ac800f97",
    "YangMills/RG/BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectanglePhysicalInverseProducerAudit.lean":
        "f76816c437267de73c6e10f6eaacdd80e2d5fcf3cfdd9d97fe2ee94c34595a21",
}
runner.QUEUE = [
    (
        "neumann_mass_reflection_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP89NeumannMassReflection",
        ],
        None,
    ),
    (
        "neumann_mass_reflection_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP89NeumannMassReflectionAudit.lean",
        ],
        2,
    ),
    (
        "neumann_precision_three_species_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP89NeumannPrecisionThreeSpecies",
        ],
        None,
    ),
    (
        "neumann_precision_three_species_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP89NeumannPrecisionThreeSpeciesAudit.lean",
        ],
        2,
    ),
    (
        "physical_neumann_inverse_producer_focal",
        [
            "lake", "build",
            "YangMills.RG."
            "BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectanglePhysicalInverseProducer",
        ],
        None,
    ),
    (
        "physical_neumann_inverse_producer_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/"
            "BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectanglePhysicalInverseProducerAudit.lean",
        ],
        7,
    ),
]


if __name__ == "__main__":
    try:
        from google.colab import runtime

        runtime.unassign = lambda: print(
            "RUNTIME_UNASSIGN_DEFERRED_TO_LAUNCHER=1", flush=True
        )
    except ImportError:
        pass
    runner_exit = runner.main()
    try:
        from google.colab import files

        files.download(str(runner.ARCHIVE))
        print("EVIDENCE_DOWNLOAD_REQUESTED=1", flush=True)
    except Exception as error:
        print("EVIDENCE_DOWNLOAD_ERROR=" + repr(error), flush=True)
    raise SystemExit(runner_exit)
