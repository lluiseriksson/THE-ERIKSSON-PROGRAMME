#!/usr/bin/env python3
"""Fresh Colab seal for the CMP89 rectangle reflection inverse scaffolding."""

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
    "cmp89_neumann_reflection_inverse_base", BASE_RUNNER
)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED_DECLARATIONS = {
    "YangMills.RG.CMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectangleReflectionRepresentation",
    "YangMills.RG.cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectangleReflectionRepresentation_eq_series",
    "YangMills.RG.cmp89Eq248PhysicalFullLatticeGreenRealAction",
    "YangMills.RG.CMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectanglePhysicalReflectionRepresentation",
    "YangMills.RG.cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectanglePhysicalReflectionRepresentation_eq_series",
    "YangMills.RG.finitePiLpScalarKernelOperator",
    "YangMills.RG.finitePiLpScalarKernelOperator_single",
    "YangMills.RG.cmp89NeumannScalarReflectionKernel",
    "YangMills.RG.cmp89NeumannScalarReflectionOperator",
    "YangMills.RG.cmp89NeumannScalarReflectionOperator_single",
    "YangMills.RG.cmp89NeumannReflectionSeries_smul",
    "YangMills.RG.cmp89CanonicalNeumannReflectionRepresentation_of_rightInverse",
    "YangMills.RG.summable_cmp89Eq248PhysicalRealNeumannReflection_sum",
}
SEEN_DECLARATIONS: set[str] = set()


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
    if not names.issubset(EXPECTED_DECLARATIONS):
        raise RuntimeError("AXIOM_DECLARATION_MISMATCH=" + repr(sorted(names)))
    SEEN_DECLARATIONS.update(names)
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
    if (
        "YangMills.RG.summable_cmp89Eq248PhysicalRealNeumannReflection_sum"
        in names
        and SEEN_DECLARATIONS != EXPECTED_DECLARATIONS
    ):
        raise RuntimeError(
            "FINAL_AXIOM_DECLARATION_MISMATCH="
            + repr(sorted(SEEN_DECLARATIONS))
        )


runner.parse_axioms = parse_axioms_exact
runner.RUNNER_REV = "cmp89-neumann-reflection-inverse-cold-v1"
runner.SOURCE_SHA = "cdd859ba99671e83a1ef2b3d8119a4e376a97ced"
runner.ROOT = Path("/content/hrpoly-cmp89-neumann-reflection-inverse-cold")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp89-neumann-reflection-inverse-cold-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp89-neumann-reflection-inverse-cold-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp89-neumann-reflection-inverse-cold-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectangleReflectionRepresentation.lean":
        "f3cc06c780ac08dab545646303cc24abb4a4f3b6d611eb090f8975333178bb7f",
    "YangMills/RG/BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectangleReflectionRepresentationAudit.lean":
        "ab96c9e06c46bfcb98bfc9b55d73bcb3dac6f2956ebc04b8058da0371cf3583b",
    "YangMills/RG/BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectanglePhysicalReflectionRepresentation.lean":
        "773c1940c132dc0f298061a9a91b79061724907a341809e5ae8f5774aa14f9ae",
    "YangMills/RG/BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectanglePhysicalReflectionRepresentationAudit.lean":
        "9c28fc57c3c33c3acdbf968f7b64b03a2dff102a46050e6baa7713356a888422",
    "YangMills/RG/BalabanCMP89NeumannScalarReflectionOperator.lean":
        "699ca04c04c31900aa23a750d417bf3b716411df785794a6701aa3321d68f70e",
    "YangMills/RG/BalabanCMP89NeumannScalarReflectionOperatorAudit.lean":
        "a0a0fbebbefa2833c9435afd822ea76d35e331f30a45762b2469cbde4d085d73",
    "YangMills/RG/BalabanCMP89CanonicalNeumannReflectionInverseProducer.lean":
        "62bcfd6336e1a8582393acc38f0fb9153a9c54bfc5d59c291b523a1f52e1d9d7",
    "YangMills/RG/BalabanCMP89CanonicalNeumannReflectionInverseProducerAudit.lean":
        "44882d0ec10fe5cfa6fa156acb2a5551e8156cbdd46a3c94c951a5984e03fdfe",
    "YangMills/RG/BalabanCMP89NeumannPhysicalRealReflectionSummability.lean":
        "d5b982f8f5715a42f56f9f3b57df334deb33c37dd6aed048840e5c18137d8312",
    "YangMills/RG/BalabanCMP89NeumannPhysicalRealReflectionSummabilityAudit.lean":
        "c950ba2f4ca36bc88c8d8ef8846a2cf600af7040cbe65d88191753ae01584a12",
}
runner.QUEUE = [
    (
        "neumann_rectangle_specialization_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectangleReflectionRepresentation"],
        None,
    ),
    (
        "neumann_rectangle_specialization_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectangleReflectionRepresentationAudit.lean"],
        2,
    ),
    (
        "neumann_rectangle_physical_specialization_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectanglePhysicalReflectionRepresentation"],
        None,
    ),
    (
        "neumann_rectangle_physical_specialization_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectanglePhysicalReflectionRepresentationAudit.lean"],
        3,
    ),
    (
        "neumann_scalar_reflection_operator_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89NeumannScalarReflectionOperator"],
        None,
    ),
    (
        "neumann_scalar_reflection_operator_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP89NeumannScalarReflectionOperatorAudit.lean"],
        6,
    ),
    (
        "neumann_reflection_inverse_producer_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89CanonicalNeumannReflectionInverseProducer"],
        None,
    ),
    (
        "neumann_reflection_inverse_producer_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP89CanonicalNeumannReflectionInverseProducerAudit.lean"],
        1,
    ),
    (
        "neumann_physical_real_summability_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89NeumannPhysicalRealReflectionSummability"],
        None,
    ),
    (
        "neumann_physical_real_summability_audit",
        ["lake", "env", "lean", "YangMills/RG/BalabanCMP89NeumannPhysicalRealReflectionSummabilityAudit.lean"],
        1,
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
