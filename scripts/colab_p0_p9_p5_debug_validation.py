#!/usr/bin/env python3
"""Colab-only diagnostic gate for the repaired P5 physical scale dictionary."""

import hashlib
from pathlib import Path
import urllib.request


P4B_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "305262842fa9a541d70bc2eb662ac8c892954526/"
    "scripts/colab_p0_p9_p4b_debug_validation.py"
)
P4B_RUNNER_SHA256 = (
    "23ba26bd50547c0a234b5d72795bbf7de97748c8e08036ec789f2c83b45cfa13"
)
with urllib.request.urlopen(P4B_RUNNER_URL) as response:
    p4b_source = response.read()
measured = hashlib.sha256(p4b_source).hexdigest()
print("P4B_RUNNER_TRANSPORT_SHA256=" + measured, flush=True)
if measured != P4B_RUNNER_SHA256:
    raise RuntimeError("P4B_RUNNER_TRANSPORT_HASH_MISMATCH")
p4b_namespace = {"__name__": "p4b_debug_configuration"}
exec(compile(p4b_source, P4B_RUNNER_URL, "exec"), p4b_namespace)

runner = p4b_namespace["runner"]
P5_PATH = "tmp/P5PhysicalGreenScaleDictionary.lean"
P5_AUDIT_PATH = "tmp/P5PhysicalGreenScaleDictionaryAudit.lean"

runner.RUNNER_REV = "p0-p9-p5-debug-v1"
runner.SOURCE_SHA = "305262842fa9a541d70bc2eb662ac8c892954526"
runner.ROOT = Path("/content/hrpoly-p0-p9-p5-debug")
runner.EVIDENCE = Path("/content/hrpoly-p0-p9-p5-debug-evidence")
runner.ARCHIVE = Path("/content/hrpoly-p0-p9-p5-debug-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-p0-p9-p5-debug-paths.txt")
runner.SOURCE_BLOBS = {
    **runner.SOURCE_BLOBS,
    P5_PATH: "7f154c1ae924e025e59c7636e5e63745089c959ca26adf20feb8a79d8181d73f",
    P5_AUDIT_PATH: "0a829127d5a2bc9316efc6106b9e6cd062db41939feafd8c21697ffccf07b992",
}
runner.QUEUE.extend([
    (
        "p5_physical_green_scale_dictionary",
        ["lake", "env", "lean", P5_PATH,
         "-o", ".lake/build/lib/lean/tmp/P5PhysicalGreenScaleDictionary.olean"],
        None,
    ),
    (
        "p5_physical_green_scale_dictionary_audit",
        ["lake", "env", "lean", P5_AUDIT_PATH],
        None,
    ),
])


if __name__ == "__main__":
    raise SystemExit(runner.main())
