#!/usr/bin/env python3
"""Template for the post-C6d Eq. (3.35) consumer cold queue.

Replace the seal SHA and all seven Git-blob SHA-256 placeholders only after
the localized retained source tower has emitted literal FINAL_STATUS=PASS and
its selective seal commit exists.  This file is preparation only and must not
be executed with placeholders.
"""

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "__C6D_SEAL_SHA__"
BASE_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    f"{SOURCE_SHA}/scripts/colab_qprime_row_validation.py"
)
BASE_SHA256 = "__BASE_RUNNER_SHA256__"
BASE_PATH = Path("/content/colab_qprime_row_validation.py")

if SOURCE_SHA.startswith("__") or BASE_SHA256.startswith("__"):
    raise RuntimeError("C6D_EQ335_CONSUMER_TEMPLATE_NOT_PINNED")

with urllib.request.urlopen(BASE_URL) as response:
    base_source = response.read()
measured = hashlib.sha256(base_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + measured, flush=True)
if measured != BASE_SHA256:
    raise RuntimeError("C6D_EQ335_CONSUMER_BASE_HASH_MISMATCH")
BASE_PATH.write_bytes(base_source)
spec = importlib.util.spec_from_file_location("c6d_eq335_consumer_base", BASE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("C6D_EQ335_CONSUMER_BASE_IMPORT_FAILED")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

F1 = "YangMills/RG/BalabanCMP99Eq335PhysicalLocalizedRetainedTower.lean"
A1 = "YangMills/RG/BalabanCMP99Eq335PhysicalLocalizedRetainedTowerAudit.lean"
F2 = "YangMills/RG/BalabanCMP99Eq335PhysicalLocalizedRetainedTowerOfSourceRegion.lean"
A2 = "YangMills/RG/BalabanCMP99Eq335PhysicalLocalizedRetainedTowerOfSourceRegionAudit.lean"
F3 = "YangMills/RG/BalabanCMP99Eq335PhysicalRegularityClassLocalizedRetainedTower.lean"
A3 = "YangMills/RG/BalabanCMP99Eq335PhysicalRegularityClassLocalizedRetainedTowerAudit.lean"
ROOT_MODULE = "YangMillsCore.lean"

runner.RUNNER_REV = "c6d-eq335-localized-retained-consumers-cold-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-c6d-eq335-consumers")
runner.EVIDENCE = Path("/content/hrpoly-c6d-eq335-consumers-evidence")
runner.ARCHIVE = Path("/content/hrpoly-c6d-eq335-consumers-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-c6d-eq335-consumers-paths.txt")
runner.SOURCE_BLOBS = {
    F1: "__F1_SHA256__",
    A1: "__A1_SHA256__",
    F2: "__F2_SHA256__",
    A2: "__A2_SHA256__",
    F3: "__F3_SHA256__",
    A3: "__A3_SHA256__",
    ROOT_MODULE: "__ROOT_SHA256__",
}

runner.QUEUE = [
    ("c6d_eq335_retained_focal",
     ["lake", "build", "YangMills.RG.BalabanCMP99Eq335PhysicalLocalizedRetainedTower"], None),
    ("c6d_eq335_retained_audit", ["lake", "env", "lean", A1], 2),
    ("c6d_eq335_source_region_focal",
     ["lake", "build", "YangMills.RG.BalabanCMP99Eq335PhysicalLocalizedRetainedTowerOfSourceRegion"], None),
    ("c6d_eq335_source_region_audit", ["lake", "env", "lean", A2], 2),
    ("c6d_eq335_regularity_class_focal",
     ["lake", "build", "YangMills.RG.BalabanCMP99Eq335PhysicalRegularityClassLocalizedRetainedTower"], None),
    ("c6d_eq335_regularity_class_audit", ["lake", "env", "lean", A3], 2),
    ("c6d_eq335_consumers_root", ["lake", "build", "YangMillsCore"], None),
]


if __name__ == "__main__":
    raise SystemExit(runner.main())
