#!/usr/bin/env python3
"""Instrumental Colab gate for the independent CMP99 (3.42) scalar prefix."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


SOURCE_SHA = "9040a8298027c520faec5042a9a03134ac9b782d"
PARENT_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "26078282adad34a477ad7ab79649d49a14558b41/"
    "scripts/colab_regional_prefix_green_block_owner_decay_validation.py"
)
PARENT_RUNNER_SHA256 = (
    "1e239ab30d12aca72d4c3b89623fd177fcd0a2e3001d57d9d391f41fcf7faa8e"
)
PARENT_RUNNER_PATH = Path(
    "/content/colab_regional_prefix_green_block_owner_decay_validation.py"
)


payload = urllib.request.urlopen(PARENT_RUNNER_URL, timeout=60).read()
measured = hashlib.sha256(payload).hexdigest()
print("PARENT_RUNNER_SHA256=" + measured, flush=True)
if measured != PARENT_RUNNER_SHA256:
    raise RuntimeError("PARENT_RUNNER_HASH_MISMATCH")
PARENT_RUNNER_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location(
    "cmp99_common_scalar_prefix_parent", PARENT_RUNNER_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("PARENT_RUNNER_IMPORT_SPEC_MISSING")
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)

runner = parent.runner
runner.RUNNER_REV = "cmp99-common-scalar-prefix-v2"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-cmp99-common-scalar-prefix")
runner.EVIDENCE = Path("/content/hrpoly-cmp99-common-scalar-prefix-evidence")
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp99-common-scalar-prefix-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp99-common-scalar-prefix-paths.txt"
)
runner.SOURCE_BLOBS = {
    "YangMills/RG/FinitePiLpBlockLocalizedSupMonotone.lean":
        "de9cbe7f7e64f7d4ba2ae0b213794e8d3db76cc0b84efbe0019f8a1fbeb3a8c0",
    "YangMills/RG/FinitePiLpBlockLocalizedSupMonotoneAudit.lean":
        "46d359d508dd759fae02bc6364485ef1169042a7c9b9ffc98cfa86b56972a3d5",
    "YangMills/RG/BalabanCMP99Eq342CommonAmplitude.lean":
        "a81c80181df498beb6ef167d190ae85b9ea473e39636c4f819229d925300c449",
    "YangMills/RG/BalabanCMP99Eq342CommonAmplitudeAudit.lean":
        "6b0cb618aee7e97fd8e584233cd4680defe1e6c1844835bb4f097f65e6ba5a03",
}
runner.QUEUE = [
    (
        "block_localized_sup_mono_focal",
        [
            "lake", "build",
            "YangMills.RG.FinitePiLpBlockLocalizedSupMonotone",
        ],
        None,
    ),
    (
        "block_localized_sup_mono_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/FinitePiLpBlockLocalizedSupMonotoneAudit.lean",
        ],
        1,
    ),
    (
        "cmp99_common_amplitude_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99Eq342CommonAmplitude",
        ],
        None,
    ),
    (
        "cmp99_common_amplitude_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99Eq342CommonAmplitudeAudit.lean",
        ],
        6,
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
        from google.colab import files

        files.download(str(runner.ARCHIVE))
        print("EVIDENCE_DOWNLOAD_REQUESTED=1", flush=True)
    except Exception as error:
        print("EVIDENCE_DOWNLOAD_ERROR=" + repr(error), flush=True)
    raise SystemExit(code)
