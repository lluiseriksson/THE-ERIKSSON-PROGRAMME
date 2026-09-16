#!/usr/bin/env python3
"""Lightweight synthetic pass/fail test for the cold-evidence validator."""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import tarfile
import tempfile
import zipfile
from pathlib import Path


HERE = Path(__file__).resolve().parent
AUDITOR = HERE / "audit_step8b22_cold_evidence.py"
SOURCE = "534493728038813f3772f8b3b073237f4da1884e"
WORKFLOW = "b05ef65af97a95752d1c929e30749d886d425d8d"
MATHLIB = "07642720480157414db592fa85b626dafb71355b"
URL = (
    "https://github.com/leanprover/lean4/releases/download/v4.29.0-rc6/"
    "lean-4.29.0-rc6-linux.tar.zst"
)
ASSET = "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
INNER = "cmp99-finite-grid-aliasing-evidence.tar.gz"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path: Path, text: str) -> None:
    path.write_text(text, encoding="utf-8", newline="\n")


def make_fixture(base: Path) -> tuple[Path, Path]:
    root = base / "extracted"
    evidence = root / "evidence"
    evidence.mkdir(parents=True)
    write(
        evidence / "checkpoint.txt",
        f"SOURCE_SHA={SOURCE}\nACTUAL_HEAD={SOURCE}\nWORKFLOW_SHA={WORKFLOW}\nCOLD_MODE=true\n",
    )
    write(
        evidence / "toolchain.txt",
        f"TOOLCHAIN_URL={URL}\nTOOLCHAIN_ASSET_SHA256={ASSET}\n"
        f"{'a' * 64}  /tmp/lean-toolchain/bin/lean\n"
        f"{'b' * 64}  /tmp/lean-toolchain/bin/lake\n"
        "Lean (version 4.29.0-rc6, synthetic)\nLake version 5.0.0-src+synthetic\n",
    )
    write(evidence / "mathlib.txt", f"MATHLIB_SHA={MATHLIB}\n")
    write(evidence / "text-guard.log", "LEAN_OVERLAY_TEXT_OK files=2 source=synthetic\n")
    write(evidence / "import-prefix-guard.log", "LEAN_IMPORT_PREFIX_OK files=2\n")
    write(
        evidence / "stages.txt",
        "STAGE=cmp99_finite_grid_aliasing_focal STARTED=2026-08-17T00:00:00Z CMD=lake build x\n"
        "STAGE=cmp99_finite_grid_aliasing_focal EXIT=0 ENDED=2026-08-17T00:02:03Z\n"
        "STAGE=cmp99_finite_grid_aliasing_audit STARTED=2026-08-17T00:02:04Z CMD=lake env lean y\n"
        "STAGE=cmp99_finite_grid_aliasing_audit EXIT=0 ENDED=2026-08-17T00:02:11Z\n",
    )
    write(
        evidence / "cmp99_finite_grid_aliasing_focal.log",
        "Build completed successfully (123 jobs).\n",
    )
    axiom_names = ["Classical.choice", "Quot.sound", "propext"]
    write(
        evidence / "cmp99_finite_grid_aliasing_audit.log",
        "".join(
            f"'synthetic{i}' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
            for i in range(7)
        ),
    )
    write(evidence / "axioms.json", json.dumps([axiom_names] * 7, indent=2) + "\n")
    write(evidence / "FINAL_STATUS", "FINAL_STATUS=PASS\n")
    write(evidence / "overlay-paths.txt", "source.lean\naudit.lean\n")
    write(evidence / "lake-update.log", "synthetic\n")
    write(evidence / "cache-get.log", "synthetic\n")

    manifest_targets = sorted(path for path in evidence.iterdir() if path.is_file())
    write(
        evidence / "SHA256SUMS",
        "".join(f"{sha(path)}  evidence/{path.name}\n" for path in manifest_targets),
    )

    inner = root / INNER
    with tarfile.open(inner, "w:gz") as packed:
        for path in sorted(evidence.iterdir()):
            packed.add(path, arcname=f"evidence/{path.name}")
    write(evidence / "ARCHIVE_SHA256", f"{sha(inner)}  {INNER}\n")

    outer = base / "artifact.zip"
    with zipfile.ZipFile(outer, "w", compression=zipfile.ZIP_DEFLATED) as packed:
        for path in sorted(root.rglob("*")):
            if path.is_file():
                packed.write(path, path.relative_to(root).as_posix())
    return root, outer


def run(root: Path, outer: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(AUDITOR), "--artifact-root", str(root), "--outer-zip", str(outer)],
        check=False,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="step8b22-evidence-test-") as raw:
        root, outer = make_fixture(Path(raw))
        positive = run(root, outer)
        if positive.returncode != 0 or "STEP8B22_COLD_EVIDENCE_OK" not in positive.stdout:
            print(positive.stdout, end="")
            print(positive.stderr, end="", file=sys.stderr)
            return 1

        write(root / "evidence" / "checkpoint.txt", "SOURCE_SHA=tampered\n")
        negative = run(root, outer)
        if negative.returncode == 0 or "STEP8B22_COLD_EVIDENCE_FAIL" not in negative.stdout:
            print("negative tamper test did not fail closed", file=sys.stderr)
            return 1

    print("STEP8B22_COLD_EVIDENCE_SELFTEST_OK positive=pass tamper=fail_closed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
