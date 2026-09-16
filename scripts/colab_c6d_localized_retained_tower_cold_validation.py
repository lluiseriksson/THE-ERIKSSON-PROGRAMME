#!/usr/bin/env python3
"""Cold seal for the C6d localized retained Q-prime tower.

The immutable PRE-VALIDATION source checkpoint is ``SOURCE_SHA``.  This
runner creates a fresh Colab checkout without restoring ``.lake/build``,
verifies the promoted source blobs, builds the focal producer and its axiom
audit, and then checks every repository consumer through ``YangMillsCore``.
It produces compiler evidence only; it does not remove PRE-VALIDATION or move
the terminal ``20/41`` counter.
"""

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "3738ddb64155a2d85f6d3609d05d5b71114ca498"
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
    raise RuntimeError("C6D_LOCALIZED_RETAINED_BASE_HASH_MISMATCH")
BASE_PATH.write_bytes(base_source)
spec = importlib.util.spec_from_file_location("c6d_localized_retained_base", BASE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("C6D_LOCALIZED_RETAINED_BASE_IMPORT_FAILED")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

SOURCE = "YangMills/RG/BalabanCMP99SourceLocalizedRetainedTower.lean"
AUDIT = "YangMills/RG/BalabanCMP99SourceLocalizedRetainedTowerAudit.lean"
ROOT_MODULE = "YangMillsCore.lean"

runner.RUNNER_REV = "c6d-localized-retained-tower-cold-v9"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-c6d-localized-retained-tower")
runner.EVIDENCE = Path("/content/hrpoly-c6d-localized-retained-tower-evidence")
runner.ARCHIVE = Path("/content/hrpoly-c6d-localized-retained-tower-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-c6d-localized-retained-tower-paths.txt")
runner.SOURCE_BLOBS = {
    SOURCE: "a0126fc772b50d066752f95b356dd963b9edb412dfc6caac4eef55f6b72e752a",
    AUDIT: "6333e4f75eca47726a94ff441658ba777dc064cdeee22ad5a37ce24293648d41",
    ROOT_MODULE: "dabba854357f0abf6b2d994e5a96efc8271358d6c45c66dea9a087cfa4bb2479",
    "YangMills/RG/BalabanCMP99Eq335PhysicalLocalizedRetainedTower.lean":
        "442e3f85f7392859e8456a48e5f31060b3c906a0f15c854e5e6ad7918f638dbc",
    "YangMills/RG/BalabanCMP99Eq335PhysicalLocalizedRetainedTowerAudit.lean":
        "55d372987cd7e4f21143f53d78cb6851d83495a31fd64817d971a4defc0a521c",
    "YangMills/RG/BalabanCMP99Eq335PhysicalLocalizedRetainedTowerOfSourceRegion.lean":
        "d7910783d4b197ce80f1eb206597bb8a94e7f025f9ba07afebabec2666dfed1d",
    "YangMills/RG/BalabanCMP99Eq335PhysicalLocalizedRetainedTowerOfSourceRegionAudit.lean":
        "3a43f4db35a374160b9aadf37913cf29b1e9547dc1b9a94fa10d25dcaf40bd0d",
    "YangMills/RG/BalabanCMP99Eq335PhysicalRegularityClassLocalizedRetainedTower.lean":
        "3bdd93588528470c67ef7f73d80e8a0e01c05f921e675c84987ae21bed273d70",
    "YangMills/RG/BalabanCMP99Eq335PhysicalRegularityClassLocalizedRetainedTowerAudit.lean":
        "aefd4126cf1182f13f2c5d10ade4d903ad71e63e59c7aabe9924704c491f4896",
}

runner.QUEUE = [
    (
        "c6d_axiom_readout_coverage",
        [
            "python3",
            "scripts/check_lean_axiom_readout_coverage.py",
            "--paths-from",
            "tmp/C6D-TRANSITIVE-PREVALIDATION-PATHS.txt",
        ],
        None,
    ),
    (
        "c6d_localized_retained_tower_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP99SourceLocalizedRetainedTower"],
        None,
    ),
    (
        "c6d_localized_retained_tower_audit",
        ["lake", "env", "lean", AUDIT],
        3,
    ),
    (
        "c6d_localized_retained_tower_root",
        ["lake", "build", "YangMillsCore"],
        None,
    ),
]


if __name__ == "__main__":
    raise SystemExit(runner.main())
