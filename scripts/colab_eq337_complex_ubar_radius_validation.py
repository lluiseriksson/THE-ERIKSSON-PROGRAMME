#!/usr/bin/env python3
"""Colab diagnostic gate for the literal complex Eq. (3.37) Ubar radius.

The immutable source checkpoint contains scratch PRE-VALIDATION modules.  The
runner materializes them in dependency order under their intended
``YangMills.RG`` olean names, audits every public declaration, and stops at the
first real error.  It does not promote source, remove PRE-VALIDATION, attain a
terminal scalar window, or move ``20/41``.
"""

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "b1357760890c9551dd9786da0f691d652bf21eda"
BASE_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    f"{SOURCE_SHA}/scripts/colab_qprime_row_validation.py"
)
BASE_SHA256 = "d06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee"
BASE_PATH = Path("/content/colab_qprime_row_validation.py")

with urllib.request.urlopen(BASE_URL) as response:
    base_source = response.read()
measured = hashlib.sha256(base_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + measured, flush=True)
if measured != BASE_SHA256:
    raise RuntimeError("COMPLEX_UBAR_RADIUS_BASE_HASH_MISMATCH")
BASE_PATH.write_bytes(base_source)
spec = importlib.util.spec_from_file_location("complex_ubar_radius_base", BASE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("COMPLEX_UBAR_RADIUS_BASE_IMPORT_FAILED")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

PAIRS = [
    ("BalabanCMP99ComplexUbarSpecialLinear", 13),
    ("BalabanCMP99ComplexUbarCoordinateExponent", 8),
    ("BalabanCMP99Eq337PhysicalComplexPerturbedLinkRadius", 5),
    ("BalabanCMP99ComplexFourFactorDeviation", 2),
    ("BalabanCMP99Eq337PhysicalComplexWilsonLineRadius", 10),
    ("BalabanCMP99ComplexLocalizedUbarBackground", 4),
    ("BalabanCMP99Eq337PhysicalComplexUbarDeviationRadius", 10),
]

runner.RUNNER_REV = "eq337-complex-ubar-radius-debug-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-eq337-complex-ubar-radius")
runner.EVIDENCE = Path("/content/hrpoly-eq337-complex-ubar-radius-evidence")
runner.ARCHIVE = Path("/content/hrpoly-eq337-complex-ubar-radius-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-eq337-complex-ubar-radius-paths.txt")
runner.SOURCE_BLOBS = {
    "tmp/BalabanCMP99ComplexUbarSpecialLinear.draft.lean":
        "1b3986d813a17a18378839bfd65d3f7c35f007ffc3b7587dba3571326f3f737c",
    "tmp/BalabanCMP99ComplexUbarSpecialLinearAudit.draft.lean":
        "46147664fa74ba119a8b4b9ecdfa2a49572c3988e7509c51ad845ca09fb57c37",
    "tmp/BalabanCMP99ComplexUbarCoordinateExponent.draft.lean":
        "101ef9c949ecb2a568762236b7daecccb56fab049341a311314bcb115379d7c9",
    "tmp/BalabanCMP99ComplexUbarCoordinateExponentAudit.draft.lean":
        "dd4cec0564c8a1b3263113a231ae1a8fd5c365db15db54bf8d638c72e1bc2ad9",
    "tmp/BalabanCMP99Eq337PhysicalComplexPerturbedLinkRadius.draft.lean":
        "aae17f83297f96c27fe1a44800166c53fa8bd390f2265e7f4d88f67af9048984",
    "tmp/BalabanCMP99Eq337PhysicalComplexPerturbedLinkRadiusAudit.draft.lean":
        "004dec0c3ba76a6e98e57203ba0b1758761193c40e2abc907e5beed30249e4d7",
    "tmp/BalabanCMP99ComplexFourFactorDeviation.draft.lean":
        "039b6d203abcb3f834ce7c24b2a8e0f5b8e1f9154a1926371ee6e47c0ed4286f",
    "tmp/BalabanCMP99ComplexFourFactorDeviationAudit.draft.lean":
        "92839a61d39512e60edfcf79925f80aaddc950be4ec7056b5e067e532092e751",
    "tmp/BalabanCMP99Eq337PhysicalComplexWilsonLineRadius.draft.lean":
        "51909e08c4471d658b3e0f13aa0528480f7e199e70739e932df9a412dc500afa",
    "tmp/BalabanCMP99Eq337PhysicalComplexWilsonLineRadiusAudit.draft.lean":
        "9167f0f8c0ecf3ad2988198dbe42b60ae2580c9b960b35a5acd24883232f1df7",
    "tmp/BalabanCMP99ComplexLocalizedUbarBackground.draft.lean":
        "98f563ea4143314a77088f2110eeb3b14883fee618711dbf1e6fc2d769f07603",
    "tmp/BalabanCMP99ComplexLocalizedUbarBackgroundAudit.draft.lean":
        "9d4e9aabab9932edef3ef68d5aad1791008dd4a2a618922a01f11843d54dcd04",
    "tmp/BalabanCMP99Eq337PhysicalComplexUbarDeviationRadius.draft.lean":
        "f2ef2fada05612aa372880803c94ef8531a1bba8371580b816ea1c97d1f89e9f",
    "tmp/BalabanCMP99Eq337PhysicalComplexUbarDeviationRadiusAudit.draft.lean":
        "88d8ec2d94567fde7572afdf8c86b343cac53bdb112aa7e67fec40370d255ee9",
}

queue = [
    (
        "complex_ubar_radius_materialize_prerequisites",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99Eq337PhysicalComplexPerturbedBackground",
            "YangMills.RG.BalabanCMP99SourceUbarContours",
            "YangMills.RG.BalabanCMP99UbarPhysicalDeviation",
            "YangMills.RG.BalabanCMP116FourFactorLipschitz",
        ],
        None,
    ),
    (
        "complex_ubar_radius_prepare_build_dirs",
        ["mkdir", "-p", ".lake/build/lib/lean/YangMills/RG", ".lake/build/lib/lean/tmp"],
        None,
    ),
]

for index, (name, expected_axioms) in enumerate(PAIRS, start=1):
    source = f"tmp/{name}.draft.lean"
    audit = f"tmp/{name}Audit.draft.lean"
    queue.extend([
        (
            f"complex_ubar_radius_{index:02d}_{name.lower()}_source",
            [
                "lake", "env", "lean", source, "-o",
                f".lake/build/lib/lean/YangMills/RG/{name}.olean",
            ],
            None,
        ),
        (
            f"complex_ubar_radius_{index:02d}_{name.lower()}_audit",
            [
                "lake", "env", "lean", audit, "-o",
                f".lake/build/lib/lean/tmp/{name}Audit.draft.olean",
            ],
            expected_axioms,
        ),
    ])

runner.QUEUE = queue


if __name__ == "__main__":
    raise SystemExit(runner.main())
