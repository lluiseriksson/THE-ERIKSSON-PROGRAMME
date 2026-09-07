#!/usr/bin/env python3
"""Colab-only diagnostic gate for the repaired P4a scratch endpoint.

This runner checks out one immutable PRE-VALIDATION source checkpoint and
materializes only the dependency prefix needed by ``P4aPhysicalBase``.  It is
diagnostic evidence, not the cold terminal P0--P9 seal.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import re
import urllib.request


HERE = Path("/content")
SOURCE_SHA = "c920cddeb5aa636f8ed19e425b43682e9510880b"
BASE_RUNNER = HERE / "colab_qprime_row_validation.py"
BASE_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "bcc852cee5e709bff91fad7de26fa21cff754e1f/"
    "scripts/colab_qprime_row_validation.py"
)
BASE_RUNNER_SHA256 = (
    "d06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee"
)
P4A_PATH = "tmp/P4aPhysicalBase.lean"
P4A_SHA256 = (
    "be6cfff68e18bfce7f6ca4a50390baa4a1bb4681691dc1e35cd3e71dd6334f3a"
)


def fetch_exact(url: str, expected: str, label: str) -> bytes:
    with urllib.request.urlopen(url) as response:
        payload = response.read()
    measured = hashlib.sha256(payload).hexdigest()
    print(label + "_TRANSPORT_SHA256=" + measured, flush=True)
    if measured != expected:
        raise RuntimeError(label + "_TRANSPORT_HASH_MISMATCH")
    return payload


BASE_RUNNER.write_bytes(fetch_exact(
    BASE_RUNNER_URL, BASE_RUNNER_SHA256, "BASE_RUNNER"
))
SPEC = importlib.util.spec_from_file_location("p4a_debug_base_runner", BASE_RUNNER)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)

runner.RUNNER_REV = "p0-p9-p4a-debug-v1"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-p0-p9-p4a-debug")
runner.EVIDENCE = Path("/content/hrpoly-p0-p9-p4a-debug-evidence")
runner.ARCHIVE = Path("/content/hrpoly-p0-p9-p4a-debug-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-p0-p9-p4a-debug-paths.txt")
runner.SOURCE_BLOBS = {P4A_PATH: P4A_SHA256}

PROJECT_PREREQUISITES = [
    "YangMills.RG.BalabanCMP99SourceRetainedGeneratedTerminalBridge",
    "YangMills.RG.BalabanCMP99SourceTowerCoarseCovariance",
    "YangMills.RG.BalabanCMP99SourceSeparatedGeneratedPhysicalAmbientDictionary",
    "YangMills.RG.FinitePiLpTypedKernelReindexAlgebra",
]

SOURCE_PREFIX = [
    "tmp/P0CanonicalPrefixTower.lean",
    "tmp/P1CoefficientMonotonicity.lean",
    "tmp/P2SourceCoefficientCoercivity.lean",
    "tmp/P2bEffectiveQuadratic.lean",
    "tmp/P2cCoarseCovariance.lean",
    "tmp/P3ScalarRecurrence.lean",
    "tmp/P3BlockGaussianAlgebra.lean",
    "tmp/P3TypedSchurBrackets.lean",
    "tmp/P3TypedGreenInverse.lean",
    "tmp/P3SourceStepCoisometry.lean",
    "tmp/P3PhysicalScalarSpecialization.lean",
    "tmp/P3PhysicalOperatorDictionary.lean",
    "tmp/P3PhysicalGreenRecurrence.lean",
    P4A_PATH,
]

runner.QUEUE = [
    (
        "p4a_materialize_project_prerequisites",
        ["lake", "build", *PROJECT_PREREQUISITES],
        None,
    ),
    (
        "p4a_prepare_scratch_build_dir",
        ["mkdir", "-p", ".lake/build/lib/lean/tmp"],
        None,
    ),
]
for index, path in enumerate(SOURCE_PREFIX, start=1):
    stem = Path(path).stem
    stage = f"p4a_{index:02d}_{re.sub(r'[^A-Za-z0-9]+', '_', stem).lower()}"
    olean = f".lake/build/lib/lean/{Path(path).with_suffix('.olean').as_posix()}"
    runner.QUEUE.append((stage, ["lake", "env", "lean", path, "-o", olean], None))


if __name__ == "__main__":
    raise SystemExit(runner.main())
