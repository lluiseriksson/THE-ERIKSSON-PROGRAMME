#!/usr/bin/env python3
"""Fresh-checkout cold gate for the mass-uniform CMP89 full-G chain."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import re
import urllib.request


BASE_RUNNER = Path("/content/colab_qprime_row_validation.py")
BASE_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "2dfaa8634203470608cc341d36e5d1fab4a546c4/"
    "scripts/colab_qprime_row_validation.py"
)
BASE_RUNNER_SHA256 = "2f097a374361bd8e4c0f53220ffeeeb22fc06d6ccca5179aebda468d1aebee8e"

with urllib.request.urlopen(BASE_RUNNER_URL, timeout=60) as response:
    base_runner_source = response.read()
base_runner_hash = hashlib.sha256(base_runner_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + base_runner_hash, flush=True)
if base_runner_hash != BASE_RUNNER_SHA256:
    raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
BASE_RUNNER.write_bytes(base_runner_source)
spec = importlib.util.spec_from_file_location("cmp89_mass_uniform_base", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


EXPECTED = {
    401: {
        "YangMills.RG.cmp89Eq246FullSolutionDomain_of_commonRadius_massUniform",
        "YangMills.RG.cmp89Eq246PhysicalFineToFineGreenIntegrand_boundarySeam_massUniform",
        "YangMills.RG.differentiableAt_cmp89Eq246StabilizedFineToFineGreenIntegrand_of_commonRadius_massUniform",
        "YangMills.RG.intervalIntegral_cmp89Eq246PhysicalFineToFineGreenIntegrand_coordinateShift_massUniform",
    },
    402: {
        "YangMills.RG.integrable_cmp89Eq246PhysicalFineToFineGreenPartialProductIntegrand_massUniform",
        "YangMills.RG.integral_cmp89Eq246PhysicalFineToFineGreenPartialProductIntegrand_stage_succ_massUniform",
        "YangMills.RG.integral_cmp89Eq246PhysicalFineToFineGreenPartialProductIntegrand_zero_eq_four_massUniform",
        "YangMills.RG.integral_cmp89Eq246PhysicalFineToFineGreenIntegrand_eq_signed_massUniform",
        "YangMills.RG.cmp89Eq246DirectedNormalizedFullSolutionIntegral_physicalFine_eq_zero_massUniform",
        "YangMills.RG.cmp89Eq246DirectedNormalizedPhysicalFineKernel_eq_zero_massUniform",
        "YangMills.RG.norm_cmp89Eq246NormalizedPhysicalFineToFineGreen_le_massUniform",
    },
    403: {
        "YangMills.RG.continuous_cmp89Eq246CenteredFullGreenCube_massUniform",
        "YangMills.RG.cmp89Eq246CenteredFullGreenCube_faceSeam_massUniform",
        "YangMills.RG.cmp89Eq246CenteredFullGreenTorus_covering_apply",
    },
    404: {
        "YangMills.RG.cmp89UnitAddTorus_mFourier_neg_mul_stabilizedFineToFineGreen_eq_affineTarget",
        "YangMills.RG.cmp89_mFourier_mul_centeredFullGreen_physicalBrillouin_massUniform",
        "YangMills.RG.cmp89_ae_mFourier_mul_centeredFullGreen_physicalBrillouin_massUniform",
        "YangMills.RG.cmp89_mFourierCoeff_centeredFullGreen_eq_normalizedFineToFineGreen_massUniform",
    },
    405: {
        "YangMills.RG.cmp89Eq246_affineTarget_sub_source",
        "YangMills.RG.cmp89Eq246PhysicalFineGreenDecay_eq_signedLatticeWeight_massUniform",
        "YangMills.RG.summable_cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient_massUniform",
        "YangMills.RG.summable_mFourierCoeff_cmp89Eq246CenteredFullGreenTorus_massUniform",
    },
    406: {
        "YangMills.RG.cmp99FlatFiniteGridFourierSeriesSample_fullGreen_eq_torusSample_massUniform",
        "YangMills.RG.cmp99Flat_normalizedFiniteGridFullGreen_eq_residueClass_massUniform",
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
runner.RUNNER_REV = "cmp89-mass-uniform-full-g-cold-v1"
runner.SOURCE_SHA = "d773e70906ae74620b5f3ce2218e0f736541a60c"
runner.MIN_RAM_GIB = 11.0
runner.ALLOW_GPU_RUNTIME = False
runner.ROOT = Path("/content/hrpoly-cmp89-mass-uniform-full-g-cold-v1")
runner.EVIDENCE = Path("/content/hrpoly-cmp89-mass-uniform-full-g-cold-v1-evidence")
runner.ARCHIVE = Path("/content/hrpoly-cmp89-mass-uniform-full-g-cold-v1-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-cmp89-mass-uniform-full-g-cold-v1-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89Eq246MassUniformAnalyticDomain.lean": "7b424730e808bc9edcb6cf091f9b6ba258336fa88b9b47400db4ac667d10b222",
    "YangMills/RG/BalabanCMP89Eq246MassUniformAnalyticDomainAudit.lean": "7bb6e220dfcc4806a3aaae6b4036747a93560b6b6b82ab1a0ed512bce972e1c2",
    "YangMills/RG/BalabanCMP89Eq246MassUniformPhysicalContour.lean": "a3b3f4a96fe7290d2f53ca621712b075aecf5310f6e6ccefc1b503a8bb5bd453",
    "YangMills/RG/BalabanCMP89Eq246MassUniformPhysicalContourAudit.lean": "5802cc1b7a61b8a0b3f25fb5fcb82eaf90ae8fd255c4758ad201a38fc811e13c",
    "YangMills/RG/BalabanCMP89Eq246MassUniformCenteredGreenTorus.lean": "47769b52eaeb5efa7595149327cab43a43202f6028d2504fe6cfb0eef4153d62",
    "YangMills/RG/BalabanCMP89Eq246MassUniformCenteredGreenTorusAudit.lean": "f0b0cd0cc440ee9cbc20fa81df6799eea5d512eb3a839c4b1780c9f4f35f9d49",
    "YangMills/RG/BalabanCMP89Eq246MassUniformCenteredGreenCoefficientDictionary.lean": "2954932e89ba2cb43438bdacde3808d747340038cedeb81cdbc1c461936d611a",
    "YangMills/RG/BalabanCMP89Eq246MassUniformCenteredGreenCoefficientDictionaryAudit.lean": "f2bf59761841f838300e5b0b91d389b2bc4ce78310adbcfe7c8d354344ab87cd",
    "YangMills/RG/BalabanCMP89Eq246MassUniformCenteredGreenFourierSummability.lean": "e78c00a5b1da529272adecf05736f1cea51547d5ab597dc394c61b153f43637c",
    "YangMills/RG/BalabanCMP89Eq246MassUniformCenteredGreenFourierSummabilityAudit.lean": "bf8d2d01f6c2a1c9f22eed266d948ebf8207cf86d9f0cd2e022f388eee43b342",
    "YangMills/RG/BalabanCMP99FullGreenFiniteGridAliasing.lean": "89ebbd509d3d56a42034cb1c94f9e20cb7bb095c8f7a03fc81883393dc44adb5",
    "YangMills/RG/BalabanCMP99FullGreenFiniteGridAliasingAudit.lean": "978468765b91ec8c59c59d10c9680c1b181571e1ce8c58cc3dbdbe06f9467756",
}
runner.QUEUE = [
    ("mass_uniform_analytic_domain_focal", ["lake", "build", "YangMills.RG.BalabanCMP89Eq246MassUniformAnalyticDomain"], None),
    ("mass_uniform_analytic_domain_audit", ["lake", "env", "lean", "YangMills/RG/BalabanCMP89Eq246MassUniformAnalyticDomainAudit.lean"], 401),
    ("mass_uniform_physical_contour_focal", ["lake", "build", "YangMills.RG.BalabanCMP89Eq246MassUniformPhysicalContour"], None),
    ("mass_uniform_physical_contour_audit", ["lake", "env", "lean", "YangMills/RG/BalabanCMP89Eq246MassUniformPhysicalContourAudit.lean"], 402),
    ("mass_uniform_centered_green_torus_focal", ["lake", "build", "YangMills.RG.BalabanCMP89Eq246MassUniformCenteredGreenTorus"], None),
    ("mass_uniform_centered_green_torus_audit", ["lake", "env", "lean", "YangMills/RG/BalabanCMP89Eq246MassUniformCenteredGreenTorusAudit.lean"], 403),
    ("mass_uniform_centered_green_coefficient_dictionary_focal", ["lake", "build", "YangMills.RG.BalabanCMP89Eq246MassUniformCenteredGreenCoefficientDictionary"], None),
    ("mass_uniform_centered_green_coefficient_dictionary_audit", ["lake", "env", "lean", "YangMills/RG/BalabanCMP89Eq246MassUniformCenteredGreenCoefficientDictionaryAudit.lean"], 404),
    ("mass_uniform_centered_green_fourier_summability_focal", ["lake", "build", "YangMills.RG.BalabanCMP89Eq246MassUniformCenteredGreenFourierSummability"], None),
    ("mass_uniform_centered_green_fourier_summability_audit", ["lake", "env", "lean", "YangMills/RG/BalabanCMP89Eq246MassUniformCenteredGreenFourierSummabilityAudit.lean"], 405),
    ("full_green_finite_grid_aliasing_focal", ["lake", "build", "YangMills.RG.BalabanCMP99FullGreenFiniteGridAliasing"], None),
    ("full_green_finite_grid_aliasing_audit", ["lake", "env", "lean", "YangMills/RG/BalabanCMP99FullGreenFiniteGridAliasingAudit.lean"], 406),
]


if __name__ == "__main__":
    saved_unassign = None
    try:
        from google.colab import runtime

        saved_unassign = runtime.unassign
        runtime.unassign = lambda: print("RUNTIME_RETAINED_FOR_DEBUG_OR_EVIDENCE=1", flush=True)
    except ImportError:
        pass
    try:
        raise SystemExit(runner.main())
    finally:
        if saved_unassign is not None:
            from google.colab import runtime

            runtime.unassign = saved_unassign
