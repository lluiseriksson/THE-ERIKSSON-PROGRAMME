#!/usr/bin/env python3
"""Pinned Colab gate for the complex forced-recursion prerequisites.

This diagnostic compiles the closed-radius scalar repro, the inverse-radius
repro, the source theorem and its audit, then the all-orientation small-field
producer and its audit.  It is stop-on-first-error and does not promote source
or move ``20/41``.
"""

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = '5931390ebf3b01b83dbd61bcc5be80fefe9bc1ae'
BASE_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    f"{SOURCE_SHA}/scripts/colab_qprime_row_validation.py"
)
BASE_SHA256 = 'd06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee'
BASE_FILE = Path("/content/colab_qprime_row_validation.py")

with urllib.request.urlopen(BASE_URL) as response:
    base_source = response.read()
measured = hashlib.sha256(base_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + measured, flush=True)
if measured != BASE_SHA256:
    raise RuntimeError("COMPLEX_RECURSION_PREREQ_BASE_HASH_MISMATCH")
BASE_FILE.write_bytes(base_source)
spec = importlib.util.spec_from_file_location(
    "complex_recursion_prereq_base", BASE_FILE
)
if spec is None or spec.loader is None:
    raise RuntimeError("COMPLEX_RECURSION_PREREQ_BASE_IMPORT_FAILED")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

runner.RUNNER_REV = 'eq337-complex-forced-recursion-prereq-v8'
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-complex-recursion-prereq")
runner.EVIDENCE = Path("/content/hrpoly-complex-recursion-prereq-evidence")
runner.ARCHIVE = Path(
    "/content/hrpoly-complex-recursion-prereq-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-complex-recursion-prereq-paths.txt"
)
runner.SOURCE_BLOBS = {
    'tmp/CMP99ComplexRadiusScalar.repro.lean': '97d73cf5b0b0b328f083aeb5716eaaf67dcb68dd6539fac4687553f333822b15',
    'tmp/CMP99ComplexInverseRadius.repro.lean': '3e71811abf32f8503db7e1730394a99c1e54531acaf8e375f2afc76f9f383d3f',
    'tmp/BalabanCMP99ComplexInverseRadius.draft.lean': 'ff9943cc7f7a398c9d653bfb2fbc86aa70f9d7e3fbd59c890b68cc5d00218dd9',
    'tmp/BalabanCMP99ComplexInverseRadiusAudit.draft.lean': 'ea2597ee82f20741fc5b1ef18665baf4b8ba47687b6c814f5e83f6d17c590d28',
    'tmp/BalabanCMP99ComplexUbarSmallFieldPropagation.draft.lean': '3ace2cbe7ab7a29205569bed357d6d9ac900e02ef64efba620de568dc5f2541c',
    'tmp/BalabanCMP99ComplexUbarSmallFieldPropagationAudit.draft.lean': '382ded9f34b3afe26072a120953848325def8d12fd76b3a33dc5e7c273f41e88',
}

runner.QUEUE = [
    (
        "complex_recursion_prereq_prepare_build_dirs",
        ["mkdir", "-p", ".lake/build/lib/lean/YangMills/RG",
         ".lake/build/lib/lean/tmp"],
        None,
    ),
    (
        "complex_radius_scalar_repro",
        [
            "lake", "env", "lean",
            "tmp/CMP99ComplexRadiusScalar.repro.lean", "-o",
            ".lake/build/lib/lean/tmp/CMP99ComplexRadiusScalar.repro.olean",
        ],
        2,
    ),
    (
        "complex_inverse_radius_repro",
        [
            "lake", "env", "lean",
            "tmp/CMP99ComplexInverseRadius.repro.lean", "-o",
            ".lake/build/lib/lean/tmp/CMP99ComplexInverseRadius.repro.olean",
        ],
        None,
    ),
    (
        "complex_recursion_prereq_materialize_dependencies",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99Eq337PhysicalComplexUbarDeviationRadius",
            "YangMills.RG.BalabanCMP99SourceUbarSmallFieldPropagation",
            "YangMills.RG.BalabanCMP99ComplexUbarSpecialLinear",
        ],
        None,
    ),
    (
        "complex_inverse_radius_source",
        [
            "lake", "env", "lean",
            "tmp/BalabanCMP99ComplexInverseRadius.draft.lean", "-o",
            ".lake/build/lib/lean/YangMills/RG/"
            "BalabanCMP99ComplexInverseRadius.olean",
        ],
        None,
    ),
    (
        "complex_inverse_radius_audit",
        [
            "lake", "env", "lean",
            "tmp/BalabanCMP99ComplexInverseRadiusAudit.draft.lean", "-o",
            ".lake/build/lib/lean/tmp/"
            "BalabanCMP99ComplexInverseRadiusAudit.draft.olean",
        ],
        1,
    ),
    (
        "complex_ubar_small_field_source",
        [
            "lake", "env", "lean",
            "tmp/BalabanCMP99ComplexUbarSmallFieldPropagation.draft.lean", "-o",
            ".lake/build/lib/lean/YangMills/RG/"
            "BalabanCMP99ComplexUbarSmallFieldPropagation.olean",
        ],
        None,
    ),
    (
        "complex_ubar_small_field_audit",
        [
            "lake", "env", "lean",
            "tmp/BalabanCMP99ComplexUbarSmallFieldPropagationAudit.draft.lean",
            "-o", ".lake/build/lib/lean/tmp/"
            "BalabanCMP99ComplexUbarSmallFieldPropagationAudit.draft.olean",
        ],
        13,
    ),
]


if __name__ == "__main__":
    raise SystemExit(runner.main())
