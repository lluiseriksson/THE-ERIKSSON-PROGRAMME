#!/usr/bin/env python3
"""Fresh-clone Colab gate for the CMP99 regional precision split brick.

This file is validation infrastructure only.  It checks the immutable source
checkpoint named by ``SOURCE_SHA`` and disconnects the Colab runtime at the
first error or after success.
"""

from __future__ import annotations

import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
import time
import traceback


RUNNER_REV = "regional-large-block-v14"
SOURCE_SHA = "c5eaba7ed47b14b738da7baef8877ca2b8c84af7"
REPO_URL = "https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git"
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.29.0-rc6"
EXPECTED_MATHLIB = "07642720480157414db592fa85b626dafb71355b"
TOOLCHAIN_URL = (
    "https://github.com/leanprover/lean4/releases/download/v4.29.0-rc6/"
    "lean-4.29.0-rc6-linux.tar.zst"
)
TOOLCHAIN_SHA256 = "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
ROOT = Path("/content/hrpoly-regional-large-block")
EVIDENCE = Path("/content/hrpoly-regional-large-block-evidence")
ARCHIVE = Path("/content/hrpoly-regional-large-block-evidence.tar.gz")
ASSET = Path("/content/lean-4.29.0-rc6-linux.tar.zst")
TOOLROOT = Path("/content/lean-4.29.0-rc6-linux")

LEGACY_QUEUE_V9 = [
    (
        "regional_fine_scale_nogo_focal",
        [
            "lake",
            "build", "YangMills.RG.BalabanCMP99SourceRegionalFineScaleNoGo",
        ],
        None,
    ),
    (
        "regional_fine_scale_nogo_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP99SourceRegionalFineScaleNoGoAudit.lean",
        ],
        3,
    ),
    (
        "regional_large_block_partition_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceRegionalLargeBlockPartition",
        ],
        None,
    ),
    (
        "regional_large_block_partition_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceRegionalLargeBlockPartitionAudit.lean",
        ],
        4,
    ),
    (
        "regional_large_block_slope_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceRegionalLargeBlockSlope",
        ],
        None,
    ),
    (
        "regional_large_block_slope_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceRegionalLargeBlockSlopeAudit.lean",
        ],
        4,
    ),
    (
        "regional_large_block_overlap_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceRegionalLargeBlockOverlap",
        ],
        None,
    ),
    (
        "regional_large_block_overlap_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceRegionalLargeBlockOverlapAudit.lean",
        ],
        2,
    ),
    (
        "regional_green_neumann_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceRegionalGreenNeumann",
        ],
        None,
    ),
    (
        "regional_green_neumann_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceRegionalGreenNeumannAudit.lean",
        ],
        11,
    ),
    (
        "typed_scalar_commutator_row_focal",
        [
            "lake", "build",
            "YangMills.RG.FinitePiLpTypedScalarCommutatorWeightedRow",
        ],
        None,
    ),
    (
        "typed_scalar_commutator_row_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/FinitePiLpTypedScalarCommutatorWeightedRowAudit.lean",
        ],
        2,
    ),
    (
        "source_overlap_sum_focal",
        ["lake", "build", "YangMills.RG.FinitePiLpSourceOverlapSum"],
        None,
    ),
    (
        "source_overlap_sum_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/FinitePiLpSourceOverlapSumAudit.lean",
        ],
        1,
    ),
    (
        "regional_defect_overlap_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceRegionalDefectOverlap",
        ],
        None,
    ),
    (
        "regional_defect_overlap_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceRegionalDefectOverlapAudit.lean",
        ],
        3,
    ),
    (
        "weighted_row_from_range_focal",
        ["lake", "build", "YangMills.RG.FinitePiLpTypedWeightedRowFromRange"],
        None,
    ),
    (
        "weighted_row_from_range_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/FinitePiLpTypedWeightedRowFromRangeAudit.lean",
        ],
        1,
    ),
    (
        "source_overlap_weighted_row_focal",
        ["lake", "build", "YangMills.RG.FinitePiLpSourceOverlapWeightedRow"],
        None,
    ),
    (
        "source_overlap_weighted_row_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/FinitePiLpSourceOverlapWeightedRowAudit.lean",
        ],
        1,
    ),
    (
        "active_fine_block_equiv_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceActiveFineBlockEquiv",
        ],
        None,
    ),
    (
        "active_fine_block_equiv_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceActiveFineBlockEquivAudit.lean",
        ],
        2,
    ),
    (
        "transported_synthesis_row_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceTransportedBlockSynthesisRowSum",
        ],
        None,
    ),
    (
        "transported_synthesis_row_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceTransportedBlockSynthesisRowSumAudit.lean",
        ],
        2,
    ),
]

REGIONAL_PRECISION_QUEUE_V10 = [
    (
        "commutator_algebra_repro",
        ["lake", "env", "lean", "/content/regional-commutator-repro.lean"],
        None,
    ),
    (
        "regional_source_precision_commutator_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceRegionalGaugePrecisionCommutator",
        ],
        None,
    ),
    (
        "regional_source_precision_commutator_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/"
            "BalabanCMP99SourceRegionalGaugePrecisionCommutatorAudit.lean",
        ],
        1,
    ),
]

QUEUE = [
    (
        "slope_algebra_repro",
        ["lake", "env", "lean", "/content/regional-slope-repro.lean"],
        None,
    ),
] + LEGACY_QUEUE_V9[4:]

ALGEBRA_REPRO = r"""import Mathlib

noncomputable section

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

example (H K Q : E →L[ℝ] E) (a : ℝ) :
    H.comp (K + a • Q) - (K + a • Q).comp H =
      (H.comp K - K.comp H) + a • (H.comp Q - Q.comp H) := by
  apply ContinuousLinearMap.ext
  intro phi
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    map_add, map_smul]
  module
"""

SLOPE_REPRO = r"""import Mathlib

noncomputable section

example (M Q depth : ℕ) :
    M ^ (depth + 2) * (2 * Q) = (2 * M ^ (depth + 2)) * Q := by
  ac_rfl

example (M depth : ℕ) [NeZero M] :
    (M : ℝ) ^ (depth + 1) / (2 * (M : ℝ) ^ (depth + 2)) =
      1 / (2 * (M : ℝ)) := by
  rw [show depth + 2 = (depth + 1) + 1 by omega, pow_succ]
  have hpow : (M : ℝ) ^ (depth + 1) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne M))
  have hM : (M : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (NeZero.ne M)
  field_simp [hpow, hM] <;> ring_nf

def sourceCoordinate (scale : ℕ) (x : Fin 4 → ℕ) : Fin 4 → ℝ :=
  fun i => (x i : ℝ) + 1 / 2 - (scale : ℝ) / 2

example (scale : ℕ) (x : Fin 4 → ℕ) :
    sourceCoordinate scale x =
      fun i => (x i : ℝ) + (1 / 2 - (scale : ℝ) / 2) := by
  funext i
  unfold sourceCoordinate
  ring
"""

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def run(stage: str, command: list[str], *, cwd: Path | None = None) -> str:
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
    record = {
        "stage": stage,
        "exit": child.returncode,
        "seconds": elapsed,
        "output_sha256": hashlib.sha256(output.encode()).hexdigest(),
    }
    RECORDS.append(record)
    print(
        "STAGE=" + stage + " EXIT=" + str(child.returncode)
        + " SECONDS=%.3f" % elapsed,
        flush=True,
    )
    if child.returncode != 0:
        raise RuntimeError("FIRST_ERROR=" + stage)
    return output


def parse_axioms(output: str, expected: int) -> None:
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    blocks = re.findall(r"dependsonaxioms:\[([^\]]*)\]", compact)
    if len(blocks) != expected:
        raise RuntimeError(f"AXIOM_BLOCK_COUNT={len(blocks)} EXPECTED={expected}")
    for index, body in enumerate(blocks):
        names = {name for name in body.split(",") if name}
        if not names.issubset(ALLOWED_AXIOMS):
            raise RuntimeError(f"AXIOM_SET_{index}={sorted(names)}")


def make_evidence(status: str, opened: str) -> tuple[str, str]:
    payload = json.dumps(
        {
            "runner_rev": RUNNER_REV,
            "source_sha": SOURCE_SHA,
            "mathlib_sha": EXPECTED_MATHLIB,
            "toolchain_asset_sha256": TOOLCHAIN_SHA256,
            "status": status,
            "opened_utc": opened,
            "closed_utc": utc_now(),
            "records": RECORDS,
        },
        sort_keys=True,
        separators=(",", ":"),
    )
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    (EVIDENCE / "evidence.json").write_text(payload + "\n", encoding="utf-8")
    if ARCHIVE.exists():
        ARCHIVE.unlink()
    with tarfile.open(ARCHIVE, "w:gz") as archive:
        archive.add(EVIDENCE, arcname=EVIDENCE.name)
    return hashlib.sha256(payload.encode()).hexdigest(), sha256(ARCHIVE)


RECORDS: list[dict[str, object]] = []


def main() -> int:
    opened = utc_now()
    status = "FAIL"
    print("RUNNER_REV=" + RUNNER_REV, flush=True)
    print("STAGE=runtime_open UTC=" + opened, flush=True)
    try:
        import psutil

        ram_gib = psutil.virtual_memory().total / 2**30
        print("RUNTIME=CPU RAM_GIB=%.2f" % ram_gib, flush=True)
        if Path("/dev/nvidia0").exists():
            raise RuntimeError("GPU_RUNTIME_NOT_AUTHORIZED")
        if ram_gib < 40:
            raise RuntimeError("HIGH_RAM_REQUIRED")

        for path in (ROOT, EVIDENCE, TOOLROOT):
            if path.exists():
                shutil.rmtree(path)
        for path in (ASSET, ARCHIVE):
            if path.exists():
                path.unlink()

        run(
            "download_toolchain",
            [
                "curl",
                "--fail",
                "--location",
                "--retry",
                "5",
                "--retry-all-errors",
                "--retry-delay",
                "2",
                "-o",
                str(ASSET),
                TOOLCHAIN_URL,
            ],
        )
        asset_hash = sha256(ASSET)
        print("TOOLCHAIN_ASSET_SHA256=" + asset_hash, flush=True)
        if asset_hash != TOOLCHAIN_SHA256:
            raise RuntimeError("TOOLCHAIN_HASH_MISMATCH")
        if shutil.which("unzstd") is None:
            run("apt_update", ["apt-get", "update", "-qq"])
            run(
                "install_zstd",
                ["apt-get", "install", "-y", "-qq", "zstd"],
            )
        TOOLROOT.mkdir(parents=True)
        run(
            "extract_toolchain",
            [
                "tar",
                "--use-compress-program=unzstd",
                "-xf",
                str(ASSET),
                "-C",
                str(TOOLROOT),
            ],
        )
        lake_candidates = list(TOOLROOT.glob("*/bin/lake"))
        if len(lake_candidates) != 1:
            raise RuntimeError("LAKE_CANDIDATE_COUNT=" + str(len(lake_candidates)))
        bindir = lake_candidates[0].parent
        os.environ["PATH"] = str(bindir) + os.pathsep + os.environ["PATH"]
        run("lean_version", ["lean", "--version"])
        run("lake_version", ["lake", "--version"])
        print("LEAN_SHA256=" + sha256(bindir / "lean"), flush=True)
        print("LAKE_SHA256=" + sha256(bindir / "lake"), flush=True)

        run("clone", ["git", "clone", "--no-tags", REPO_URL, str(ROOT)])
        run("checkout", ["git", "checkout", "--detach", SOURCE_SHA], cwd=ROOT)
        head = run("head", ["git", "rev-parse", "HEAD"], cwd=ROOT).strip()
        if head != SOURCE_SHA:
            raise RuntimeError("HEAD_MISMATCH=" + head)
        if (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip() != EXPECTED_TOOLCHAIN:
            raise RuntimeError("LEAN_TOOLCHAIN_FILE_MISMATCH")
        manifest_before = sha256(ROOT / "lake-manifest.json")
        toolchain_before = sha256(ROOT / "lean-toolchain")
        run("lake_update", ["lake", "update"], cwd=ROOT)
        if sha256(ROOT / "lake-manifest.json") != manifest_before:
            raise RuntimeError("MANIFEST_DRIFT")
        if sha256(ROOT / "lean-toolchain") != toolchain_before:
            raise RuntimeError("TOOLCHAIN_FILE_DRIFT")
        mathlib = run(
            "mathlib_pin",
            ["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"],
            cwd=ROOT,
        ).strip()
        if mathlib != EXPECTED_MATHLIB:
            raise RuntimeError("MATHLIB_PIN_MISMATCH=" + mathlib)
        run("cache_get", ["lake", "exe", "cache", "get"], cwd=ROOT)

        Path("/content/regional-slope-repro.lean").write_text(
            SLOPE_REPRO, encoding="utf-8"
        )

        for stage, command, expected_axioms in QUEUE:
            output = run(stage, command, cwd=ROOT)
            if expected_axioms is not None:
                parse_axioms(output, expected_axioms)
        status = "PASS"
    except Exception as error:
        print("ERROR=" + repr(error), flush=True)
        traceback.print_exc()
    finally:
        evidence_hash, archive_hash = make_evidence(status, opened)
        print("EVIDENCE_SHA256=" + evidence_hash, flush=True)
        print("EVIDENCE_ARCHIVE=" + str(ARCHIVE), flush=True)
        print("EVIDENCE_ARCHIVE_SHA256=" + archive_hash, flush=True)
        print("FINAL_STATUS=" + status, flush=True)
        try:
            from google.colab import runtime

            runtime.unassign()
            print("RUNTIME_UNASSIGN_REQUESTED=1", flush=True)
        except Exception as error:
            print("RUNTIME_UNASSIGN_ERROR=" + repr(error), flush=True)
    return 0 if status == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
