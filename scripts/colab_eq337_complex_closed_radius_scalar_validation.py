#!/usr/bin/env python3
"""Pinned Colab diagnostic for the proof-free closed Eq. (3.37) radius map.

This is a diagnostic-only, stop-on-first-error gate.  It compiles the
Mathlib-only scalar reproducer from one exact source checkpoint and audits
its ten public declarations.  It does not promote source, remove
PRE-VALIDATION, move ``20/41``, or claim the physical recursion closed.
"""

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "c0f711a76b3b01edb21150a4aea02ddabee17c92"
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
    raise RuntimeError("COMPLEX_CLOSED_RADIUS_BASE_HASH_MISMATCH")
BASE_FILE.write_bytes(base_source)
spec = importlib.util.spec_from_file_location("complex_closed_radius_base", BASE_FILE)
if spec is None or spec.loader is None:
    raise RuntimeError("COMPLEX_CLOSED_RADIUS_BASE_IMPORT_FAILED")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

runner.RUNNER_REV = "eq337-complex-closed-radius-scalar-diagnostic-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-complex-closed-radius-scalar")
runner.EVIDENCE = Path("/content/hrpoly-complex-closed-radius-scalar-evidence")
runner.ARCHIVE = Path("/content/hrpoly-complex-closed-radius-scalar-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-complex-closed-radius-scalar-paths.txt")
runner.SOURCE_BLOBS = {
    "tmp/CMP99ComplexClosedRadiusScalar.repro.lean":
        "170c58637f6ff88d70e95cf08ebb2073d015a0ea7248e22d71d6282fc3935962",
}
runner.QUEUE = [
    (
        "complex_closed_radius_prepare_build_dir",
        ["mkdir", "-p", ".lake/build/lib/lean/tmp"],
        None,
    ),
    (
        "complex_closed_radius_scalar_repro",
        [
            "lake", "env", "lean",
            "tmp/CMP99ComplexClosedRadiusScalar.repro.lean", "-o",
            ".lake/build/lib/lean/tmp/CMP99ComplexClosedRadiusScalar.repro.olean",
        ],
        10,
    ),
]


if __name__ == "__main__":
    raise SystemExit(runner.main())
