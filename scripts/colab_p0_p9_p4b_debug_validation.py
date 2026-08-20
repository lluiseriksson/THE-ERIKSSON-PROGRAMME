#!/usr/bin/env python3
"""Colab-only diagnostic gate for the repaired P4b scratch endpoint."""

import hashlib
from pathlib import Path
import re
import urllib.request


P4A_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "48a2b9d0dbb87db864bd8fc4c879841ae8516240/"
    "scripts/colab_p0_p9_p4a_debug_validation.py"
)
P4A_RUNNER_SHA256 = (
    "f20beb84b6998944d11c80889db130e990f847f5968e73290a0c65f572b4836f"
)
with urllib.request.urlopen(P4A_RUNNER_URL) as response:
    p4a_source = response.read()
measured = hashlib.sha256(p4a_source).hexdigest()
print("P4A_RUNNER_TRANSPORT_SHA256=" + measured, flush=True)
if measured != P4A_RUNNER_SHA256:
    raise RuntimeError("P4A_RUNNER_TRANSPORT_HASH_MISMATCH")
p4a_namespace = {"__name__": "p4a_debug_configuration"}
exec(compile(p4a_source, P4A_RUNNER_URL, "exec"), p4a_namespace)

runner = p4a_namespace["runner"]
P4A_PATH = p4a_namespace["P4A_PATH"]
P4A_SHA256 = p4a_namespace["P4A_SHA256"]
P4B_PATH = "tmp/P4bFiniteTelescoping.lean"
P4B_SHA256 = (
    "1ed93de817c913d951b04e5391a7a1752465d78efbbd6cb014a8863de3dcf6c3"
)

runner.RUNNER_REV = "p0-p9-p4b-debug-v1"
runner.SOURCE_SHA = "b177491c0596389857b92603224656898c65eeaa"
runner.ROOT = Path("/content/hrpoly-p0-p9-p4b-debug")
runner.EVIDENCE = Path("/content/hrpoly-p0-p9-p4b-debug-evidence")
runner.ARCHIVE = Path("/content/hrpoly-p0-p9-p4b-debug-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-p0-p9-p4b-debug-paths.txt")
runner.SOURCE_BLOBS = {
    P4A_PATH: P4A_SHA256,
    P4B_PATH: P4B_SHA256,
}

source_prefix = [*p4a_namespace["SOURCE_PREFIX"], P4B_PATH]
runner.QUEUE = [
    (
        "p4b_materialize_project_prerequisites",
        ["lake", "build", *p4a_namespace["PROJECT_PREREQUISITES"]],
        None,
    ),
    (
        "p4b_prepare_scratch_build_dir",
        ["mkdir", "-p", ".lake/build/lib/lean/tmp"],
        None,
    ),
]
for index, path in enumerate(source_prefix, start=1):
    stem = Path(path).stem
    stage = f"p4b_{index:02d}_{re.sub(r'[^A-Za-z0-9]+', '_', stem).lower()}"
    olean = f".lake/build/lib/lean/{Path(path).with_suffix('.olean').as_posix()}"
    runner.QUEUE.append((stage, ["lake", "env", "lean", path, "-o", olean], None))


if __name__ == "__main__":
    raise SystemExit(runner.main())
