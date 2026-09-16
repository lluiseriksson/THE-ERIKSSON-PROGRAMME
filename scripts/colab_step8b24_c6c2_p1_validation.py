#!/usr/bin/env python3
"""Colab first-error diagnostic for Step 8b.24/C6c.2 P1 only.

This runner validates the prefix Poincare monotonicity construction and its exact
eight-readout sibling audit.  It does not introduce P2--P5, attain window 15,
move a terminal counter or inhabit TermSource.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


HERE = Path("/content")
BASE_RUNNER = HERE / "colab_qprime_row_validation.py"
BASE_RUNNER_URL = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/bcc852cee5e709bff91fad7de26fa21cff754e1f/scripts/colab_qprime_row_validation.py'
BASE_RUNNER_SHA256 = 'd06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee'
with urllib.request.urlopen(BASE_RUNNER_URL) as response:
    base_runner_source = response.read()
base_runner_hash = hashlib.sha256(base_runner_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + base_runner_hash, flush=True)
if base_runner_hash != BASE_RUNNER_SHA256:
    raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
BASE_RUNNER.write_bytes(base_runner_source)
spec = importlib.util.spec_from_file_location("step8b24_c6c2_p1_base", BASE_RUNNER)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

runner.RUNNER_REV = "step8b24-c6c2-p1-v1"
runner.SOURCE_SHA = '317b540f57e598f7dea9a41f0c7278f0c674150f'
runner.ROOT = Path("/content/hrpoly-step8b24-c6c2-p1")
runner.EVIDENCE = Path("/content/hrpoly-step8b24-c6c2-p1-evidence")
runner.ARCHIVE = Path("/content/hrpoly-step8b24-c6c2-p1-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-step8b24-c6c2-p1-paths.txt")
runner.SOURCE_BLOBS = {
    'YangMills/RG/BalabanCMP99SourcePrefixPoincare.lean': '548609c4f0cde8e0cfd3d91e2acb5dfae1b61c8cd533c8756f5fc4a5eb26bafc',
    'YangMills/RG/BalabanCMP99SourcePrefixPoincareAudit.lean': '5544d89773a94a3a2a233dda4e236a88eaeaed0dac917d0a54c303271a9dc523',
}
runner.QUEUE = [
    (
        "01_p1_prefix_poincare_focal",
        ["lake", "build", 'YangMills.RG.BalabanCMP99SourcePrefixPoincare'],
        None,
    ),
    (
        "02_p1_prefix_poincare_audit",
        ["lake", "env", "lean", 'YangMills/RG/BalabanCMP99SourcePrefixPoincareAudit.lean'],
        8,
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
    raise SystemExit(runner.main())
