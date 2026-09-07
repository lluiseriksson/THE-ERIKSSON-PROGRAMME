#!/usr/bin/env python3
"""Pinned cold Colab seal for the public closed Eq. (3.37) scalar module.

This is a cold, stop-on-first-error gate. It compiles the promoted scalar
module and its fifteen-declaration axiom audit from one exact source
checkpoint. It does not install the physical recursion or move ``20/41``.
"""

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "ae676b71f2bae392560db80cbadcd24e6193305a"
BASE_PATH = "scripts/colab_qprime_row_validation.py"
BASE_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    f"{SOURCE_SHA}/{BASE_PATH}"
)
BASE_SHA256 = "d06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee"
BASE_FILE = Path("/content/colab_qprime_row_validation.py")

with urllib.request.urlopen(BASE_URL) as response:
    base_source = response.read()
measured = hashlib.sha256(base_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + measured, flush=True)
if measured != BASE_SHA256:
    raise RuntimeError("COMPLEX_CLOSED_RADIUS_MODULE_BASE_HASH_MISMATCH")
BASE_FILE.write_bytes(base_source)
spec = importlib.util.spec_from_file_location("complex_closed_radius_module_base", BASE_FILE)
if spec is None or spec.loader is None:
    raise RuntimeError("COMPLEX_CLOSED_RADIUS_MODULE_BASE_IMPORT_FAILED")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

runner.RUNNER_REV = "eq337-complex-closed-radius-module-cold-v2"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-complex-closed-radius-module")
runner.EVIDENCE = Path("/content/hrpoly-complex-closed-radius-module-evidence")
runner.ARCHIVE = Path("/content/hrpoly-complex-closed-radius-module-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-complex-closed-radius-module-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99Eq337ComplexClosedRadiusScalar.lean":
        "7adfd435acf6e312c17769bda7dc739360b85735ee0f8f6af8a653275502ba01",
    "YangMills/RG/BalabanCMP99Eq337ComplexClosedRadiusScalarAudit.lean":
        "ff5a8ea1ae904fce9501fac2bcf8bbd03ff1cdeb76b68457340dc56f30dc096c",
}
runner.QUEUE = [
    (
        "complex_closed_radius_module_prepare_build_dir",
        ["mkdir", "-p", ".lake/build/lib/lean/YangMills/RG"],
        None,
    ),
    (
        "complex_closed_radius_module",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99Eq337ComplexClosedRadiusScalar.lean",
            "-o",
            ".lake/build/lib/lean/YangMills/RG/"
            "BalabanCMP99Eq337ComplexClosedRadiusScalar.olean",
        ],
        None,
    ),
    (
        "complex_closed_radius_module_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99Eq337ComplexClosedRadiusScalarAudit.lean",
        ],
        15,
    ),
]


if __name__ == "__main__":
    raise SystemExit(runner.main())
