#!/usr/bin/env python3
"""Cold seal for the promoted CMP99 (3.35)--(3.36) physical chain.

The immutable PRE-VALIDATION checkpoint is ``SOURCE_SHA``.  This runner
clones it into a fresh Colab root, verifies every promoted blob, builds the
repository root, and reruns the five promoted axiom audits explicitly.  It is
the compiler gate for the promoted paths; it does not remove their notices.
"""

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "f85f09480ffda5502cbd60884eac387ab646a8b5"
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
    raise RuntimeError("C6D_EQ336_PROMOTED_BASE_HASH_MISMATCH")
BASE_PATH.write_bytes(base_source)
spec = importlib.util.spec_from_file_location("c6d_eq336_promoted_base", BASE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("C6D_EQ336_PROMOTED_BASE_IMPORT_FAILED")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

REGULAR_CUBE = "YangMills/RG/BalabanCMP99SourceRegularCube.lean"
REGULAR_CUBE_AUDIT = "YangMills/RG/BalabanCMP99SourceRegularCubeAudit.lean"
FORWARD = "YangMills/RG/BalabanCMP99Eq335PhysicalForwardDerivative.lean"
FORWARD_AUDIT = "YangMills/RG/BalabanCMP99Eq335PhysicalForwardDerivativeAudit.lean"
WITNESS = "YangMills/RG/BalabanCMP99Eq335PhysicalRegularityWitness.lean"
WITNESS_AUDIT = "YangMills/RG/BalabanCMP99Eq335PhysicalRegularityWitnessAudit.lean"
CLASS = "YangMills/RG/BalabanCMP99Eq335PhysicalRegularityClass.lean"
CLASS_AUDIT = "YangMills/RG/BalabanCMP99Eq335PhysicalRegularityClassAudit.lean"
EQ336 = "YangMills/RG/BalabanCMP99Eq336PhysicalDStarDRegularityClass.lean"
EQ336_AUDIT = "YangMills/RG/BalabanCMP99Eq336PhysicalDStarDRegularityClassAudit.lean"
ROOT_MODULE = "YangMillsCore.lean"

runner.RUNNER_REV = "c6d-eq336-promoted-cold-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-c6d-eq336-promoted")
runner.EVIDENCE = Path("/content/hrpoly-c6d-eq336-promoted-evidence")
runner.ARCHIVE = Path("/content/hrpoly-c6d-eq336-promoted-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-c6d-eq336-promoted-paths.txt")
runner.SOURCE_BLOBS = {
    REGULAR_CUBE: "e65e10aa052d9ca948c73b4b87a3355b09edeb6b6b1a7f72dfdf7831a31ed18f",
    REGULAR_CUBE_AUDIT: "0b451dafd21056970d245368aa827038732b05396cce096d423728cfa94a44f5",
    FORWARD: "30fb2f13a28d25ce046474122afe803b667979f099f7c967cd43222cef50e45f",
    FORWARD_AUDIT: "8ad5c228bc0dc38870ea3dc3632e4602163f287cd5e01491a0caafca10fb0ec7",
    WITNESS: "f68d85e62b61811422dba41a2ad97bdf4b9789bc95c51c3251c737f7af5057a1",
    WITNESS_AUDIT: "f148ddc4c0e1b74d9ee812575f4ec2fed8a07a45ff7a86d8d7a4123ccccd6652",
    CLASS: "857b235bfed147ff96a9099bf71b5dd8a8127ad5b920dc3f6d5ecd18534efc4c",
    CLASS_AUDIT: "0317c850c08df1728200f1d2d8baf8dad8c1a0af4b06537776eafd278b9beebd",
    EQ336: "b3844d39598436eb1a4c9143b8c17e5249c20b552ac433509bab0e281ea63d2d",
    EQ336_AUDIT: "08ac168d1fb87f4272b9a73c6adac05f96d498453bc91a489de90910a9754a77",
    ROOT_MODULE: "ce96d848d7c831ca44ba1288d9b0a4277787a6486ffc3d2d4beea69c482a11fb",
}

runner.QUEUE = [
    (
        "c6d_eq336_promoted_root",
        ["lake", "build", "YangMillsCore"],
        None,
    ),
    (
        "c6d_regular_cube_promoted_audit",
        ["lake", "env", "lean", REGULAR_CUBE_AUDIT],
        7,
    ),
    (
        "c6d_eq335_forward_promoted_audit",
        ["lake", "env", "lean", FORWARD_AUDIT],
        1,
    ),
    (
        "c6d_eq335_witness_promoted_audit",
        ["lake", "env", "lean", WITNESS_AUDIT],
        8,
    ),
    (
        "c6d_eq335_class_promoted_audit",
        ["lake", "env", "lean", CLASS_AUDIT],
        3,
    ),
    (
        "c6d_eq336_promoted_audit",
        ["lake", "env", "lean", EQ336_AUDIT],
        17,
    ),
]


if __name__ == "__main__":
    raise SystemExit(runner.main())
