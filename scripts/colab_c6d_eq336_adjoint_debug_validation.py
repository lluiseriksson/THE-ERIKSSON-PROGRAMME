#!/usr/bin/env python3
"""Colab debug gate for the CMP99 (3.36) physical adjoint identity.

The immutable PRE-VALIDATION source checkpoint is ``SOURCE_SHA``.  This gate
first compiles the already-small algebraic reproduction, then the complete
scratch source.  It is diagnostic evidence only: it does not promote the
module, remove PRE-VALIDATION, or move any terminal counter.
"""

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "263a3163a6d3d2fecbb3d3508c2b01ba45c99904"
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
    raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
BASE_PATH.write_bytes(base_source)
spec = importlib.util.spec_from_file_location("c6d_eq336_debug_base", BASE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("C6D_EQ336_DEBUG_BASE_IMPORT_FAILED")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

REGULAR_CUBE_PATH = "tmp/BalabanCMP99SourceRegularCube.draft.lean"
REGULAR_CUBE_AUDIT_PATH = "tmp/BalabanCMP99SourceRegularCubeAudit.draft.lean"
FORWARD_PATH = "tmp/BalabanCMP99Eq335PhysicalForwardDerivative.draft.lean"
FORWARD_AUDIT_PATH = "tmp/BalabanCMP99Eq335PhysicalForwardDerivativeAudit.draft.lean"
WITNESS_PATH = "tmp/BalabanCMP99Eq335PhysicalRegularityWitness.draft.lean"
WITNESS_AUDIT_PATH = "tmp/BalabanCMP99Eq335PhysicalRegularityWitnessAudit.draft.lean"
CLASS_PATH = "tmp/BalabanCMP99Eq335PhysicalRegularityClass.draft.lean"
CLASS_AUDIT_PATH = "tmp/BalabanCMP99Eq335PhysicalRegularityClassAudit.draft.lean"
SOURCE_PATH = "tmp/BalabanCMP99Eq336PhysicalDStarDRegularityClass.draft.lean"
AUDIT_PATH = "tmp/BalabanCMP99Eq336PhysicalDStarDRegularityClassAudit.draft.lean"
REPRO_PATH = "tmp/CMP99DStarPairSummationByPartsRepro.lean"

runner.RUNNER_REV = "c6d-eq336-adjoint-hot-debug-v10"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-c6d-eq336-adjoint-debug")
runner.EVIDENCE = Path("/content/hrpoly-c6d-eq336-adjoint-debug-evidence")
runner.ARCHIVE = Path("/content/hrpoly-c6d-eq336-adjoint-debug-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-c6d-eq336-adjoint-debug-paths.txt")
runner.SOURCE_BLOBS = {
    REGULAR_CUBE_PATH: "99ecba48e6298980bd6443eb61aa62ec92055c64b262f539bcf4077e74019b10",
    REGULAR_CUBE_AUDIT_PATH: "433de67e650961c902f62b26b12a5ee6646c33b5dbc73c1e3fc42102b6514966",
    FORWARD_PATH: "65634e403fc0cf35029e063cb4ef35d494b653f0ef5eec290bf80dd06caadb6c",
    FORWARD_AUDIT_PATH: "72025c310ac02d756e7c9005fc006aae42ca155d9859b7a36cefa2310705fdf6",
    WITNESS_PATH: "14a29ec9fd6a0f75c22f3d38e2f8339ad80a8a2e8bcc732c4536087366a6a59e",
    WITNESS_AUDIT_PATH: "488a9b0b20f0f67b94a4a3ea1b21bb9a9325e9246512a46c0870e3ed69dbf4e4",
    CLASS_PATH: "d1995928394961cdc8c7b3651a2b304f2a3c01e1017d069ef4a92550bcab0700",
    CLASS_AUDIT_PATH: "eefa756993496832af7caa4ff322749979c6c133aa9c0cac8200f1f5001f5bec",
    SOURCE_PATH: "34d37768388a7be94ce106412a8765c78581ee1a7d9411aa200eb5b1b66ca002",
    AUDIT_PATH: "31df8715d2bbc26bfe013a4a48059876c1d12ac519e3bc6e14576968e5bc121d",
    REPRO_PATH: "b0c68923d55d2e92e946bd92699c3ebc12aaf61b37f54ccff8484f7e01adc47f",
}

runner.QUEUE = [
    (
        "c6d_eq336_materialize_prerequisites",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP98PhysicalSpecialUnitaryChart",
            "YangMills.RG.BalabanCMP99SourceScaledStratification",
            "YangMills.RG.FiniteTorusCurlDiv",
            "YangMills.RG.PhysicalGaugeCochains",
        ],
        None,
    ),
    (
        "c6d_eq336_prepare_scratch_build_dir",
        ["mkdir", "-p", ".lake/build/lib/lean/YangMills/RG", ".lake/build/lib/lean/tmp"],
        None,
    ),
    (
        "c6d_regular_cube_source",
        [
            "lake", "env", "lean", REGULAR_CUBE_PATH, "-o",
            ".lake/build/lib/lean/YangMills/RG/BalabanCMP99SourceRegularCube.olean",
        ],
        None,
    ),
    (
        "c6d_regular_cube_audit",
        [
            "lake", "env", "lean", REGULAR_CUBE_AUDIT_PATH, "-o",
            ".lake/build/lib/lean/tmp/BalabanCMP99SourceRegularCubeAudit.draft.olean",
        ],
        7,
    ),
    (
        "c6d_eq335_forward_source",
        [
            "lake", "env", "lean", FORWARD_PATH, "-o",
            ".lake/build/lib/lean/YangMills/RG/BalabanCMP99Eq335PhysicalForwardDerivative.olean",
        ],
        None,
    ),
    (
        "c6d_eq335_forward_audit",
        [
            "lake", "env", "lean", FORWARD_AUDIT_PATH, "-o",
            ".lake/build/lib/lean/tmp/BalabanCMP99Eq335PhysicalForwardDerivativeAudit.draft.olean",
        ],
        1,
    ),
    (
        "c6d_eq335_witness_source",
        [
            "lake", "env", "lean", WITNESS_PATH, "-o",
            ".lake/build/lib/lean/YangMills/RG/BalabanCMP99Eq335PhysicalRegularityWitness.olean",
        ],
        None,
    ),
    (
        "c6d_eq335_witness_audit",
        [
            "lake", "env", "lean", WITNESS_AUDIT_PATH, "-o",
            ".lake/build/lib/lean/tmp/BalabanCMP99Eq335PhysicalRegularityWitnessAudit.draft.olean",
        ],
        8,
    ),
    (
        "c6d_eq335_class_source",
        [
            "lake", "env", "lean", CLASS_PATH, "-o",
            ".lake/build/lib/lean/YangMills/RG/BalabanCMP99Eq335PhysicalRegularityClass.olean",
        ],
        None,
    ),
    (
        "c6d_eq335_class_audit",
        [
            "lake", "env", "lean", CLASS_AUDIT_PATH, "-o",
            ".lake/build/lib/lean/tmp/BalabanCMP99Eq335PhysicalRegularityClassAudit.draft.olean",
        ],
        3,
    ),
    (
        "c6d_eq336_pair_repro",
        [
            "lake", "env", "lean", REPRO_PATH, "-o",
            ".lake/build/lib/lean/tmp/CMP99DStarPairSummationByPartsRepro.olean",
        ],
        3,
    ),
    (
        "c6d_eq336_physical_adjoint_source",
        [
            "lake", "env", "lean", SOURCE_PATH, "-o",
            ".lake/build/lib/lean/YangMills/RG/BalabanCMP99Eq336PhysicalDStarDRegularityClass.olean",
        ],
        None,
    ),
    (
        "c6d_eq336_physical_adjoint_audit",
        [
            "lake", "env", "lean", AUDIT_PATH, "-o",
            ".lake/build/lib/lean/tmp/BalabanCMP99Eq336PhysicalDStarDRegularityClassAudit.draft.olean",
        ],
        18,
    ),
]


if __name__ == "__main__":
    raise SystemExit(runner.main())
