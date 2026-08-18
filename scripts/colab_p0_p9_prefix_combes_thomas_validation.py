#!/usr/bin/env python3
"""Fresh-clone Colab gate for the exact P0--P9 scratch chain.

The immutable mathematical source is ``SOURCE_SHA``.  The 39 shipped Lean
chain blobs are bound by the source checkpoint's path list and SHA-256
manifest.  One additional Mathlib-only reproducer is hash-gated separately
and runs before the project prerequisite frontier.  The queue is sequential
and stop-on-first-error.

Honest scope: a green run verifies only the per-depth P0--P9 chain.  It does
not produce uniform CMP99 (3.42) constants, the four source actions, C6c.4,
window-15 attainment, a new terminal field, or a ``TermSource`` inhabitant.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import time
import urllib.request


HERE = Path("/content")
SOURCE_SHA = "c537ea3babcc1770570f9a131e11e8f11d6806ba"
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
    "7dc25b62ac67f3c6c55866b3bf32d70c55c964ccc0c13daffe07b7dcafff72bd"
)
P2B_REPRO_PATH = "tmp/P2bEffectiveQuadraticAlgebra.repro.lean"
P2B_REPRO_SHA256 = (
    "6b0b71190cf629a3bac9e1d2f8ffe24c0ffcf157573bcbcaa5c6d8507d25764e"
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


def parse_complete_axiom_headers(output: str, expected: int) -> None:
    """Accept both textual forms emitted by ``#print axioms``.

    Lean prints a nonempty dependency list as ``depends on axioms: [...]``
    and a declaration with the empty list as ``does not depend on any
    axioms``.  Both are audit headers and both count toward the independently
    declared expected total.
    """
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    blocks = re.findall(r"dependsonaxioms:\[([^\]]*)\]", compact)
    pure = compact.count("doesnotdependonanyaxioms")
    if len(blocks) + pure != expected:
        raise RuntimeError(
            "AXIOM_HEADER_COUNT=" + str(len(blocks) + pure)
            + " EXPECTED=" + str(expected)
            + " NONEMPTY=" + str(len(blocks))
            + " EMPTY=" + str(pure)
        )
    for index, body in enumerate(blocks):
        names = {name for name in body.split(",") if name}
        if not names.issubset(runner.ALLOWED_AXIOMS):
            raise RuntimeError(f"AXIOM_SET_{index}={sorted(names)}")


# The shared runner predates Lean's empty-axiom output form.  Override only
# this parser; command execution, evidence packaging and runtime release stay
# on the immutable shared implementation.
parse_complete_axiom_headers(
    "'Fixture.allowed' depends on axioms: [propext, Quot.sound]\n"
    "'Fixture.pure' does not depend on any axioms\n",
    2,
)
runner.parse_axioms = parse_complete_axiom_headers

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
source_blobs[P2B_REPRO_PATH] = P2B_REPRO_SHA256

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
P0_P5_PROJECT_PREREQUISITES = [
    "YangMills.RG.BalabanCMP99SourceRetainedGeneratedTerminalBridge",
    "YangMills.RG.BalabanCMP99SourceTowerCoarseCovariance",
    "YangMills.RG.BalabanCMP99SourceSeparatedGeneratedPhysicalAmbientDictionary",
    "YangMills.RG.FinitePiLpTypedKernelReindexAlgebra",
]
P7_P9_PROJECT_PREREQUISITES = [
    "YangMills.RG.BalabanCMP99SourceGeneratedPhysicalAmbientDictionary",
    "YangMills.RG.BalabanCMP99SourceGeneratedRegionalFinePartition",
    "YangMills.RG.BalabanCMP99SourceSeparatedLargeBlockPartition",
    "YangMills.RG.BalabanCMP99SourceGeneratedCombesThomas",
    "YangMills.RG.BalabanCMP99SourceGeneratedRegionalCorrectionDecay",
]

runner.RUNNER_REV = "p0-p9-prefix-combes-thomas-v20"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-p0-p9-prefix-combes-thomas")
runner.EVIDENCE = Path("/content/hrpoly-p0-p9-prefix-combes-thomas-evidence")
runner.ARCHIVE = Path(
    "/content/hrpoly-p0-p9-prefix-combes-thomas-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path("/content/hrpoly-p0-p9-prefix-combes-thomas-paths.txt")
runner.SOURCE_BLOBS = source_blobs


def run_with_persistent_log(
    stage: str,
    command: list[str],
    *,
    cwd: Path | None = None,
) -> str:
    """Run one child and retain its complete combined output in evidence.

    The shared runner records a digest for each child, which is sufficient for
    a PASS but not for diagnosing a first FAIL after Colab releases its
    runtime.  This exact wrapper keeps the shared stop-on-first-error semantics
    while making the digest auditable against a stage log in the archive.
    """
    started = time.perf_counter()
    print("STAGE=" + stage + " CMD=" + json.dumps(command), flush=True)
    child = subprocess.run(
        command,
        cwd=cwd,
        env=os.environ.copy(),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    elapsed = time.perf_counter() - started
    output = child.stdout
    print(output, flush=True)
    runner.EVIDENCE.mkdir(parents=True, exist_ok=True)
    log_name = re.sub(r"[^A-Za-z0-9_.-]+", "_", stage) + ".log"
    log_path = runner.EVIDENCE / log_name
    log_path.write_text(output, encoding="utf-8")
    output_hash = hashlib.sha256(output.encode()).hexdigest()
    if hashlib.sha256(log_path.read_bytes()).hexdigest() != output_hash:
        raise RuntimeError("STAGE_LOG_HASH_MISMATCH=" + stage)
    runner.RECORDS.append(
        {
            "stage": stage,
            "exit": child.returncode,
            "seconds": elapsed,
            "output_sha256": output_hash,
            "log": log_name,
        }
    )
    print(
        "STAGE=" + stage + " EXIT=" + str(child.returncode)
        + " SECONDS=%.3f" % elapsed,
        flush=True,
    )
    if child.returncode != 0:
        raise RuntimeError("FIRST_ERROR=" + stage)
    return output


runner.run = run_with_persistent_log
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
        "p0_p9_p2b_algebra_repro",
        ["lake", "env", "lean", P2B_REPRO_PATH],
        None,
    ),
    (
        "p0_p9_materialize_project_prerequisites",
        ["lake", "build", *P0_P5_PROJECT_PREREQUISITES],
        None,
    ),
    (
        "p0_p9_prepare_scratch_build_dir",
        ["mkdir", "-p", ".lake/build/lib/lean/tmp"],
        None,
    ),
]
for index, path in enumerate(paths, start=1):
    if path == "tmp/P7SourceSeparatedAmbientPrefixPrecision.lean":
        runner.QUEUE.append(
            (
                "p0_p9_materialize_p7_p9_project_prerequisites",
                ["lake", "build", *P7_P9_PROJECT_PREREQUISITES],
                None,
            )
        )
    stem = Path(path).stem
    stage = f"p0_p9_{index:02d}_{re.sub(r'[^A-Za-z0-9]+', '_', stem).lower()}"
    command = ["lake", "env", "lean", path]
    if not path.endswith("Audit.lean"):
        # Scratch audits import their immediate source through the module name
        # ``tmp.<Stem>``.  A bare ``lean source.lean`` checks the source but does
        # not leave an olean on Lake's import path; materialize that exact olean
        # under the clone's ordinary build root before running the audit.
        olean = f".lake/build/lib/lean/{Path(path).with_suffix('.olean').as_posix()}"
        command.extend(["-o", olean])
    runner.QUEUE.append(
        (stage, command, AXIOM_COUNTS.get(path))
    )


if __name__ == "__main__":
    try:
        from google.colab import runtime

        runtime.unassign = lambda: print(
            "RUNTIME_UNASSIGN_DEFERRED_TO_LAUNCHER=1", flush=True
        )
    except ImportError:
        pass
    runner_exit = runner.main()
    try:
        from google.colab import files

        files.download(str(runner.ARCHIVE))
        print("EVIDENCE_DOWNLOAD_REQUESTED=1", flush=True)
    except Exception as error:
        print("EVIDENCE_DOWNLOAD_ERROR=" + repr(error), flush=True)
    raise SystemExit(runner_exit)
