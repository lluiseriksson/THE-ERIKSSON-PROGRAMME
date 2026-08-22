#!/usr/bin/env python3
"""Instrumental Colab gate for the per-depth physical CMP99 (3.42) assembler."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "165d6288ede6ae354d8b82c690a9a7ca564ba62e"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "3f39344e2a2e7a8ccd8e12114f7c42db6c3c142a/"
    "scripts/colab_regional_prefix_right_adjoint_owner_decay_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "2fdb08f71e1704cb15b5cc9345a9c79f74c30495ed89f9e59249917f98e204ff"
)
PARENT_RUNNER_PATH = Path(
    "/content/colab_regional_prefix_right_adjoint_owner_decay_validation.py"
)


payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "regional_prefix_eq342_certificate_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "regional-prefix-eq342-certificate-v3"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-regional-prefix-eq342-certificate")
runner.EVIDENCE = Path(
    "/content/hrpoly-regional-prefix-eq342-certificate-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-regional-prefix-eq342-certificate-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-regional-prefix-eq342-certificate-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixEq342Certificate.lean":
        "ef1c6eb2fec51350259648b7c4ec275af54138fd30038649fc4bff7dfa485e4a",
    "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixEq342CertificateAudit.lean":
        "21fb8f9cca42f15a715bb94917c1f500375be032f6c46acae72ed5c75301c573",
}
runner.QUEUE = [
    (
        "regional_prefix_eq342_certificate_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP96SourceSeparatedRegionalPrefixEq342Certificate",
        ],
        None,
    ),
    (
        "regional_prefix_eq342_certificate_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixEq342CertificateAudit.lean",
        ],
        1,
    ),
]


if __name__ == "__main__":
    try:
        from google.colab import runtime

        runtime.unassign = lambda: print(
            "RUNTIME_UNASSIGN_DEFERRED_TO_LAUNCHER=1", flush=True
        )
    except ImportError:
        pass
    code = runner.main()
    try:
        from google.colab import files, runtime

        files.download(str(runner.ARCHIVE))
        print("EVIDENCE_DOWNLOAD_REQUESTED=1", flush=True)
        print("RUNTIME_UNASSIGN_REQUESTED=1", flush=True)
        runtime.unassign()
    except ImportError:
        pass
    raise SystemExit(code)
