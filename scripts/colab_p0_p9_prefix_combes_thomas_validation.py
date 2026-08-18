#!/usr/bin/env python3
"""Fresh-clone Colab gate for the exact P0--P9 scratch chain.

The immutable mathematical source is ``SOURCE_SHA``.  The 39 shipped Lean
blobs are bound by the source checkpoint's path list and SHA-256 manifest;
both transport objects are hash-gated before the shared validation runner is
entered.  The queue is sequential and stop-on-first-error.

Honest scope: a green run verifies only the per-depth P0--P9 chain.  It does
not produce uniform CMP99 (3.42) constants, the four source actions, C6c.4,
window-15 attainment, a new terminal field, or a ``TermSource`` inhabitant.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import re
import urllib.request


HERE = Path("/content")
SOURCE_SHA = "3af413563b2f71c250e9e7bbd4972efca436ad55"
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
PATHS_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    f"THE-ERIKSSON-PROGRAMME/{SOURCE_SHA}/tmp/P0-P9-SCRATCH-PATHS.txt"
)
PATHS_SHA256 = (
    "fec594c0fba52e14f8cc1e1ba886202fcdf2e425de2c93e56dbf59feebb2fa61"
)
MANIFEST_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    f"THE-ERIKSSON-PROGRAMME/{SOURCE_SHA}/tmp/P0-P9-SCRATCH-MANIFEST.sha256"
)
MANIFEST_SHA256 = (
    "71da54fe12b77f7288a33c4edb6130733b288cc0b2ba3e3a3d081e0469e4f3f9"
)


def fetch_exact(url: str, expected: str, label: str) -> bytes:
    with urllib.request.urlopen(url) as response:
        payload = response.read()
    measured = hashlib.sha256(payload).hexdigest()
    print(label + "_TRANSPORT_SHA256=" + measured, flush=True)
    if measured != expected:
        raise RuntimeError(label + "_TRANSPORT_HASH_MISMATCH")
    return payload


base_runner_source = fetch_exact(
    BASE_RUNNER_URL, BASE_RUNNER_SHA256, "BASE_RUNNER"
)
BASE_RUNNER.write_bytes(base_runner_source)
SPEC = importlib.util.spec_from_file_location("p0_p9_base_runner", BASE_RUNNER)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)

paths_payload = fetch_exact(PATHS_URL, PATHS_SHA256, "P0_P9_PATHS")
manifest_payload = fetch_exact(
    MANIFEST_URL, MANIFEST_SHA256, "P0_P9_MANIFEST"
)
paths = [line for line in paths_payload.decode("utf-8-sig").splitlines() if line]
source_blobs: dict[str, str] = {}
for number, line in enumerate(
    manifest_payload.decode("utf-8-sig").splitlines(), start=1
):
    match = re.fullmatch(r"([0-9A-Fa-f]{64})\s+(.+)", line)
    if match is None:
        raise RuntimeError(f"P0_P9_BAD_MANIFEST_ROW={number}")
    source_blobs[match.group(2)] = match.group(1).lower()
if len(paths) != 39 or list(source_blobs) != paths:
    raise RuntimeError(f"P0_P9_TRANSPORT_SCOPE_MISMATCH={len(paths)}/{len(source_blobs)}")

# These counts are an independent audit contract, not values inferred from
# the source files at runtime.  A missing or extra readout therefore fails.
AXIOM_COUNTS = {
    "tmp/P0CanonicalPrefixTowerAudit.lean": 10,
    "tmp/P1CoefficientMonotonicityAudit.lean": 8,
    "tmp/P2SourceCoefficientCoercivityAudit.lean": 26,
    "tmp/P2bEffectiveQuadraticAudit.lean": 10,
    "tmp/P2cCoarseCovarianceAudit.lean": 24,
    "tmp/P3ScalarRecurrenceAudit.lean": 9,
    "tmp/P3BlockGaussianAlgebraAudit.lean": 2,
    "tmp/P3TypedSchurBracketsAudit.lean": 8,
    "tmp/P3TypedGreenInverseAudit.lean": 8,
    "tmp/P3SourceStepCoisometryAudit.lean": 2,
    "tmp/P3PhysicalScalarSpecializationAudit.lean": 4,
    "tmp/P3PhysicalOperatorDictionaryAudit.lean": 3,
    "tmp/P3PhysicalGreenRecurrenceAudit.lean": 3,
    "tmp/P3PhysicalGreenRecurrenceAggregateAudit.lean": 18,
    "tmp/P4aPhysicalBaseAudit.lean": 12,
    "tmp/P4bFiniteTelescopingAudit.lean": 14,
    "tmp/P5PhysicalGreenScaleDictionaryAudit.lean": 13,
    "tmp/P7SourceSeparatedAmbientPrefixPrecisionAudit.lean": 8,
    "tmp/P8SourceSeparatedRegionalPrefixGreenAudit.lean": 5,
    "tmp/P9SourceSeparatedPrefixCombesThomasAudit.lean": 12,
}
if set(AXIOM_COUNTS) != {path for path in paths if path.endswith("Audit.lean")}:
    raise RuntimeError("P0_P9_AXIOM_SCOPE_MISMATCH")

# The scratch chain imports these tracked project modules directly.  The
# Mathlib cache does not materialize local ``YangMills`` oleans, so a fresh
# clone must build this exact prerequisite frontier before invoking ``lean``
# on P0.  This is infrastructure only: none of these targets is a P0--P9
# conclusion, and SOURCE_SHA plus the 39 mathematical blobs remain unchanged.
PROJECT_PREREQUISITES = [
    "YangMills.RG.BalabanCMP99SourceRetainedGeneratedTerminalBridge",
    "YangMills.RG.BalabanCMP99SourceTowerCoarseCovariance",
    "YangMills.RG.BalabanCMP99SourceSeparatedGeneratedPhysicalAmbientDictionary",
    "YangMills.RG.FinitePiLpTypedKernelReindexAlgebra",
    "YangMills.RG.BalabanCMP99SourceGeneratedPhysicalAmbientDictionary",
    "YangMills.RG.BalabanCMP99SourceGeneratedRegionalFinePartition",
    "YangMills.RG.BalabanCMP99SourceSeparatedLargeBlockPartition",
    "YangMills.RG.BalabanCMP99SourceGeneratedCombesThomas",
    "YangMills.RG.BalabanCMP99SourceGeneratedRegionalCorrectionDecay",
]

runner.RUNNER_REV = "p0-p9-prefix-combes-thomas-v3"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-p0-p9-prefix-combes-thomas")
runner.EVIDENCE = Path("/content/hrpoly-p0-p9-prefix-combes-thomas-evidence")
runner.ARCHIVE = Path(
    "/content/hrpoly-p0-p9-prefix-combes-thomas-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path("/content/hrpoly-p0-p9-prefix-combes-thomas-paths.txt")
runner.SOURCE_BLOBS = source_blobs
runner.QUEUE = [
    (
        "p0_p9_static_gate",
        ["python3", "tmp/audit_p0_p9_diagnostic.py"],
        None,
    ),
    (
        "p0_p9_static_selftest",
        ["python3", "tmp/test_p0_p9_diagnostic.py"],
        None,
    ),
    (
        "p0_p9_materialize_project_prerequisites",
        ["lake", "build", *PROJECT_PREREQUISITES],
        None,
    ),
]
for index, path in enumerate(paths, start=1):
    stem = Path(path).stem
    stage = f"p0_p9_{index:02d}_{re.sub(r'[^A-Za-z0-9]+', '_', stem).lower()}"
    runner.QUEUE.append(
        (stage, ["lake", "env", "lean", path], AXIOM_COUNTS.get(path))
    )


if __name__ == "__main__":
    try:
        from google.colab import runtime

        runtime.unassign = lambda: print(
            "RUNTIME_UNASSIGN_DEFERRED_TO_LAUNCHER=1", flush=True
        )
    except ImportError:
        pass
    raise SystemExit(runner.main())
