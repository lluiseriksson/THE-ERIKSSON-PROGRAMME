#!/usr/bin/env python3
"""Retained-runtime diagnostic for physical endpoint reflection.

This runner reuses the exact graph retained by the orientation cold seal and
the preceding negative-domain diagnostic.  It hash-gates one immutable
PRE-VALIDATION checkpoint and stops at the first focal or axiom error.  A
PASS is diagnostic only and cannot retire PRE-VALIDATION notices.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


HERE = Path("/content")
BASE = HERE / "colab_cmp99_negative_physical_domain_retained_hot_v2.py"
BASE_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "f59173b1/"
    "scripts/colab_cmp99_negative_physical_domain_retained_hot.py"
)
BASE_SHA256 = (
    "21ff6063a43dc8dc463c88b2d39e09947e6144f6bf7a39d8ea667f7381968712"
)

with urllib.request.urlopen(BASE_URL, timeout=60) as response:
    source = response.read()
digest = hashlib.sha256(source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + digest, flush=True)
if digest != BASE_SHA256:
    raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
BASE.write_bytes(source)

spec = importlib.util.spec_from_file_location("cmp99_physical_reflection_base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load retained base: {BASE}")
negative = importlib.util.module_from_spec(spec)
spec.loader.exec_module(negative)
runner = negative.runner

runner.RUNNER_REV = "cmp99-physical-endpoint-reflection-retained-hot-v2"
runner.SOURCE_SHA = "4d61fbd43d48887da9009ba92941b83673acfaa0"
runner.ROOT = Path("/content/hrpoly-cmp99-full-point-source-orientation-cold-v3")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp99-physical-endpoint-reflection-retained-hot-v2-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp99-physical-endpoint-reflection-retained-hot-v2-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp99-physical-endpoint-reflection-retained-hot-v2-paths.txt"
)

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceFlatFullPointSourcePhysicalEndpointReflection.lean":
        "3a426062c3556db30441c4e467384dd83991e9aaed8c06d0cac4428667cb7c53",
    "YangMills/RG/BalabanCMP99SourceFlatFullPointSourcePhysicalEndpointReflectionAudit.lean":
        "2d0eff0e5e438f56e7e48622c4b22d9fd3afd5b2e37b9ef58aa0320728f0e749",
}

runner.QUEUE = [
    (
        "physical_endpoint_reflection_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceFlatFullPointSourcePhysicalEndpointReflection",
        ],
        None,
    ),
    (
        "physical_endpoint_reflection_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceFlatFullPointSourcePhysicalEndpointReflectionAudit.lean",
        ],
        frozenset({
            "YangMills.RG.cmp99SourceFlatFullPointSourcePhysicalFineToFineGreenIntegrand_neg_swap",
        }),
    ),
]


if __name__ == "__main__":
    raise SystemExit(negative.endpoint.hot.retained_main())
