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


SOURCE_SHA = "ce684e9a695d915b126d38a1a430e056b5679522"
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

SOURCE_PATH = "tmp/BalabanCMP99Eq336PhysicalDStarDRegularityClass.draft.lean"
AUDIT_PATH = "tmp/BalabanCMP99Eq336PhysicalDStarDRegularityClassAudit.draft.lean"
REPRO_PATH = "tmp/CMP99DStarPairSummationByPartsRepro.lean"

runner.RUNNER_REV = "c6d-eq336-adjoint-hot-debug-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-c6d-eq336-adjoint-debug")
runner.EVIDENCE = Path("/content/hrpoly-c6d-eq336-adjoint-debug-evidence")
runner.ARCHIVE = Path("/content/hrpoly-c6d-eq336-adjoint-debug-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-c6d-eq336-adjoint-debug-paths.txt")
runner.SOURCE_BLOBS = {
    SOURCE_PATH: "8813cc3094eef6d2b12431bf33e407c69961b27e94456be343b40988549c9c48",
    AUDIT_PATH: "31df8715d2bbc26bfe013a4a48059876c1d12ac519e3bc6e14576968e5bc121d",
    REPRO_PATH: "40883bfcd9f13e4d8fd1dcfa9c3fca405d89fbb821c66ec75e33b00592890131",
}

runner.QUEUE = [
    (
        "c6d_eq336_materialize_prerequisites",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99Eq335PhysicalRegularityClass",
            "YangMills.RG.FiniteTorusCurlDiv",
        ],
        None,
    ),
    (
        "c6d_eq336_prepare_scratch_build_dir",
        ["mkdir", "-p", ".lake/build/lib/lean/tmp"],
        None,
    ),
    (
        "c6d_eq336_pair_repro",
        [
            "lake", "env", "lean", REPRO_PATH, "-o",
            ".lake/build/lib/lean/tmp/CMP99DStarPairSummationByPartsRepro.olean",
        ],
        4,
    ),
    (
        "c6d_eq336_physical_adjoint_source",
        [
            "lake", "env", "lean", SOURCE_PATH, "-o",
            ".lake/build/lib/lean/tmp/BalabanCMP99Eq336PhysicalDStarDRegularityClass.draft.olean",
        ],
        None,
    ),
]


if __name__ == "__main__":
    raise SystemExit(runner.main())
