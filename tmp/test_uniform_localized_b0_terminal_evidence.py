#!/usr/bin/env python3
"""Synthetic PASS and tamper tests for the B0 terminal evidence validator."""

from __future__ import annotations

import hashlib
import subprocess
import sys
import tarfile
import tempfile
import zipfile
from pathlib import Path


HERE = Path(__file__).resolve().parent
AUDITOR = HERE / "audit_uniform_localized_b0_terminal_evidence.py"
SOURCE = "73bb1a2008c557840a91e50d8abe6b874947f7ee"
CONTROL = "ebccd7e8811d639587563fe060705811163e1c57"
MATHLIB = "07642720480157414db592fa85b626dafb71355b"
URL = "https://github.com/leanprover/lean4/releases/download/v4.29.0-rc6/lean-4.29.0-rc6-linux.tar.zst"
ASSET = "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
INNER = "source-flow-uniform-localized-b0-evidence.tar.gz"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path: Path, text: str) -> None:
    path.write_text(text, encoding="utf-8", newline="\n")


def make_fixture(base: Path) -> tuple[Path, Path]:
    root = base / "extracted"
    evidence = root / "evidence"
    evidence.mkdir(parents=True)
    write(evidence / "checkpoint.txt",
          f"SOURCE_SHA={SOURCE}\nACTUAL_SOURCE_HEAD={SOURCE}\nCONTROL_SHA={CONTROL}\n"
          f"GITHUB_SHA={CONTROL}\nCOLD_MODE=true\n")
    write(evidence / "toolchain.txt",
          f"TOOLCHAIN_URL={URL}\nTOOLCHAIN_ASSET_SHA256={ASSET}\n"
          f"{'a' * 64}  /tmp/toolchain/lean\n{'b' * 64}  /tmp/toolchain/lake\n"
          "Lean (version 4.29.0-rc6, synthetic)\nLake version synthetic\n")
    write(evidence / "mathlib.txt", f"MATHLIB_SHA={MATHLIB}\n")
    statuses = {
        "focal.status": "source_flow_uniform_point_source_b0_focal",
        "uniform-audit.status": "source_flow_uniform_point_source_b0_audit",
        "localized-focal.status": "source_flow_localized_field_b0_focal",
        "localized-audit.status": "source_flow_localized_field_b0_audit",
    }
    for filename, stage in statuses.items():
        write(evidence / filename, f"stage={stage} exit=0 seconds=7\n")
    write(evidence / "focal.log", "Build completed successfully (100 jobs).\n")
    write(evidence / "localized-focal.log", "Build completed successfully (2 jobs).\n")
    block = "'x' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
    write(evidence / "uniform-audit.log", block * 5)
    write(evidence / "localized-audit.log", block * 2)
    names = "Classical.choice,Quot.sound,propext"
    write(evidence / "uniform-axioms.txt",
          "".join(f"uniform_axiom_block_{i}={names}\n" for i in range(1, 6)))
    write(evidence / "localized-axioms.txt",
          "".join(f"localized_axiom_block_{i}={names}\n" for i in range(1, 3)))
    write(evidence / "lake-update.log", "synthetic\n")
    write(evidence / "cache-get.log", "synthetic\n")
    write(evidence / "FINAL_STATUS", "FINAL_STATUS=PASS\n")

    targets = sorted(path for path in evidence.iterdir() if path.is_file())
    write(evidence / "SHA256SUMS",
          "".join(f"{sha(path)}  evidence/{path.name}\n" for path in targets))
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
    return subprocess.run([sys.executable, str(AUDITOR), "--artifact-root", str(root),
                           "--outer-zip", str(outer)], check=False, capture_output=True,
                          text=True, encoding="utf-8")


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="uniform-localized-b0-test-") as raw:
        root, outer = make_fixture(Path(raw))
        positive = run(root, outer)
        if positive.returncode != 0 or "UNIFORM_LOCALIZED_B0_TERMINAL_EVIDENCE_OK" not in positive.stdout:
            print(positive.stdout, end="")
            print(positive.stderr, end="", file=sys.stderr)
            return 1
        write(root / "evidence" / "FINAL_STATUS", "FINAL_STATUS=FAIL_OR_INCOMPLETE\n")
        negative = run(root, outer)
        if negative.returncode == 0 or "UNIFORM_LOCALIZED_B0_TERMINAL_EVIDENCE_FAIL" not in negative.stdout:
            print("tamper test did not fail closed", file=sys.stderr)
            return 1
    print("UNIFORM_LOCALIZED_B0_TERMINAL_EVIDENCE_SELFTEST_OK positive=pass tamper=fail_closed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
