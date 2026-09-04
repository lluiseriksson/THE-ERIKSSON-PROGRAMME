#!/usr/bin/env python3
"""Retained-runtime diagnostic for the negative physical Eq. (2.46) domain.

This runner reuses the exact fresh graph retained by the preceding cold
orientation seal.  It fetches and hash-gates one immutable PRE-VALIDATION
source checkpoint and stops at the first focal or axiom error.  A PASS is hot
diagnostic evidence only and cannot retire PRE-VALIDATION notices.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


HERE = Path("/content")
BASE = HERE / "colab_cmp99_full_endpoint_reflection_retained_hot_v2.py"
BASE_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "71b47b53/"
    "scripts/colab_cmp99_full_endpoint_reflection_retained_hot.py"
)
BASE_SHA256 = (
    "262e1daa07610a2d93cef65e327165d24d8b2819501d2e1d4c271e66ece5033b"
)

with urllib.request.urlopen(BASE_URL, timeout=60) as response:
    source = response.read()
digest = hashlib.sha256(source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + digest, flush=True)
if digest != BASE_SHA256:
    raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
BASE.write_bytes(source)

spec = importlib.util.spec_from_file_location("cmp99_negative_domain_base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load retained base: {BASE}")
endpoint = importlib.util.module_from_spec(spec)
spec.loader.exec_module(endpoint)
runner = endpoint.runner

runner.RUNNER_REV = "cmp99-negative-physical-domain-retained-hot-v1"
runner.SOURCE_SHA = "d5414bb4b3c89946662b12be51da641a614d3cab"
runner.ROOT = Path("/content/hrpoly-cmp99-full-point-source-orientation-cold-v3")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp99-negative-physical-domain-retained-hot-v1-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp99-negative-physical-domain-retained-hot-v1-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp99-negative-physical-domain-retained-hot-v1-paths.txt"
)

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceNegativePhysicalDomain.lean":
        "15afb0ea67d2b0a29240cae1be31f457622036dc60ce8550a8e5deb570758d47",
    "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceNegativePhysicalDomainAudit.lean":
        "cd257952fd0e9c1d25ab09e1b619ecdf5f2db38588c16543231e57edd1dff6c4",
}

runner.QUEUE = [
    (
        "negative_physical_domain_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceFlatFullPointSourceNegativePhysicalDomain",
        ],
        None,
    ),
    (
        "negative_physical_domain_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceNegativePhysicalDomainAudit.lean",
        ],
        frozenset({
            "YangMills.RG.cmp99SourceFlatFullPointSourceSolutionDomain_neg_physical",
        }),
    ),
]


if __name__ == "__main__":
    raise SystemExit(endpoint.hot.retained_main())
