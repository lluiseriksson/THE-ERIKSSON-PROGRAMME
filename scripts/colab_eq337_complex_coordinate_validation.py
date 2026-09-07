#!/usr/bin/env python3
"""Fresh-clone validation of the Eq. (3.37) complex coordinate boundary.

``SOURCE_SHA`` is a PRE-VALIDATION source checkpoint.  This runner validates
the real derivative prerequisite, the complex derivative, and the explicit
complex-linear equivalence with ``sl(N,C)`` used by the perturbed background.
It is an intermediate brick: it does not edit ``YangMillsCore.lean``, remove
PRE-VALIDATION, attain window 15, or move the terminal ``20/41`` counter.
"""

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "b70735b82216a0ab1cd9a3bd4e195db1426a83fe"
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
    raise RuntimeError("EQ337_COMPLEX_COORDINATE_BASE_HASH_MISMATCH")
BASE_PATH.write_bytes(base_source)
spec = importlib.util.spec_from_file_location("eq337_complex_coordinate_base", BASE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("EQ337_COMPLEX_COORDINATE_BASE_IMPORT_FAILED")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

REAL = "YangMills/RG/BalabanCMP99Eq337PhysicalRealCovariantDerivative.lean"
REAL_AUDIT = (
    "YangMills/RG/"
    "BalabanCMP99Eq337PhysicalRealCovariantDerivativeAudit.lean"
)
COMPLEX = "YangMills/RG/BalabanCMP99Eq337PhysicalComplexCovariantDerivative.lean"
COMPLEX_AUDIT = (
    "YangMills/RG/"
    "BalabanCMP99Eq337PhysicalComplexCovariantDerivativeAudit.lean"
)
BACKGROUND = (
    "YangMills/RG/"
    "BalabanCMP99Eq337PhysicalComplexPerturbedBackground.lean"
)
BACKGROUND_AUDIT = (
    "YangMills/RG/"
    "BalabanCMP99Eq337PhysicalComplexPerturbedBackgroundAudit.lean"
)

runner.RUNNER_REV = "eq337-complex-coordinate-fresh-v4"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-eq337-complex-coordinate")
runner.EVIDENCE = Path("/content/hrpoly-eq337-complex-coordinate-evidence")
runner.ARCHIVE = Path("/content/hrpoly-eq337-complex-coordinate-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-eq337-complex-coordinate-paths.txt")
runner.SOURCE_BLOBS = {
    REAL: "fd13c9b57f0b60aef49134106c7d0e4e3fdf4aeafda9c3574f2e5fa63e67f02a",
    REAL_AUDIT: "e15b8887cfe9259c8ff44d3cab05d51f110bd0573b1054696b15280b1e48c56f",
    COMPLEX: "11986d4d32c0fc1458ac35a9ce52de10afe022823c49287d11360ca1a12d0086",
    COMPLEX_AUDIT: "9ec01c5f72dbc1cf49eabfa3c12a84b8bbd9602950c47b35745352c0c0e1fcb9",
    BACKGROUND: "c97b3b7a63694882b7508e2cc6ccea6e903c1f97bb7bfd371a549e3c397ee1a6",
    BACKGROUND_AUDIT: "d85ee70b4d46e9b0993154eb71afddf77b8121b1259c175708445190fbbb7bd9",
}

runner.QUEUE = [
    (
        "eq337_axiom_readout_coverage",
        [
            "python3",
            "scripts/check_lean_axiom_readout_coverage.py",
            "--paths-from",
            "tmp/C6D-EQ337-COMPLEX-COORDINATE-PROMOTION-PATHS.txt",
        ],
        None,
    ),
    (
        "eq337_real_covariant_derivative_focal",
        [
            "lake",
            "build",
            "YangMills.RG.BalabanCMP99Eq337PhysicalRealCovariantDerivative",
        ],
        None,
    ),
    (
        "eq337_real_covariant_derivative_audit",
        ["lake", "env", "lean", REAL_AUDIT],
        8,
    ),
    (
        "eq337_complex_covariant_derivative_focal",
        [
            "lake",
            "build",
            "YangMills.RG.BalabanCMP99Eq337PhysicalComplexCovariantDerivative",
        ],
        None,
    ),
    (
        "eq337_complex_covariant_derivative_audit",
        ["lake", "env", "lean", COMPLEX_AUDIT],
        23,
    ),
    (
        "eq337_complex_coordinate_background_focal",
        [
            "lake",
            "build",
            "YangMills.RG.BalabanCMP99Eq337PhysicalComplexPerturbedBackground",
        ],
        None,
    ),
    (
        "eq337_complex_coordinate_background_audit",
        ["lake", "env", "lean", BACKGROUND_AUDIT],
        26,
    ),
]


if __name__ == "__main__":
    raise SystemExit(runner.main())
