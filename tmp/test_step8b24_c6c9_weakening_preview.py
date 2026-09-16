#!/usr/bin/env python3
"""Synthetic positive/tamper tests for the C6c.9 weakening preview."""

from __future__ import annotations

import hashlib
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = "audit_step8b24_c6c9_weakening_preview.py"
PAIR = (
    "FinitePiLpBlockLocalizedSupMonotone.draft.lean",
    "FinitePiLpBlockLocalizedSupMonotoneAudit.draft.lean",
)


def fixture_at(parent: Path) -> Path:
    fixture = parent / "repo"
    (fixture / "tmp").mkdir(parents=True)
    (fixture / "YangMills/RG").mkdir(parents=True)
    for name in (*PAIR, SCRIPT):
        shutil.copyfile(ROOT / "tmp" / name, fixture / "tmp" / name)
    (fixture / "YangMills/RG/FinitePiLpBlockLocalizedSup.lean").write_text(
        "-- prerequisite fixture\n", encoding="utf-8", newline="\n"
    )
    return fixture


def run(fixture: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, f"tmp/{SCRIPT}"], cwd=fixture, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
    )


def require_failure(result: subprocess.CompletedProcess[str], token: str) -> None:
    if result.returncode == 0 or token not in result.stdout:
        raise SystemExit(
            f"C6C9_WEAKENING_SELFTEST_EXPECTED_FAILURE={token}\n{result.stdout}"
        )


def update_pinned_hash(script: Path, old: str, blob: Path) -> None:
    replacement = hashlib.sha256(blob.read_bytes()).hexdigest().upper()
    text = script.read_text(encoding="utf-8").replace(old, replacement)
    script.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="c6c9-weakening-") as directory:
        base = Path(directory)

        fixture = fixture_at(base / "positive")
        result = run(fixture)
        if result.returncode != 0 or "C6C9_WEAKENING_PREVIEW_OK" not in result.stdout:
            raise SystemExit("C6C9_WEAKENING_SELFTEST_POSITIVE_FAILED\n" + result.stdout)

        fixture = fixture_at(base / "source-tamper")
        source = fixture / "tmp" / PAIR[0]
        source.write_bytes(source.read_bytes() + b"\n")
        require_failure(run(fixture), "C6C9_WEAKENING_RAW_HASH_MISMATCH")

        fixture = fixture_at(base / "audit-scope")
        audit = fixture / "tmp" / PAIR[1]
        audit.write_text(
            audit.read_text(encoding="utf-8").replace("#print axioms", "-- removed"),
            encoding="utf-8", newline="\n",
        )
        update_pinned_hash(
            fixture / "tmp" / SCRIPT,
            "A94C9A9F50922F2CDC4DFF6C790C11687A46C3BFEBA3EADE66F06E53B77702F0",
            audit,
        )
        require_failure(run(fixture), "C6C9_WEAKENING_AUDIT_READOUT_SCOPE")

        fixture = fixture_at(base / "missing-prerequisite")
        (fixture / "YangMills/RG/FinitePiLpBlockLocalizedSup.lean").unlink()
        require_failure(run(fixture), "C6C9_WEAKENING_PREREQUISITE_MISSING")

        fixture = fixture_at(base / "collision")
        (fixture / "YangMills/RG/FinitePiLpBlockLocalizedSupMonotone.lean").write_text(
            "-- collision\n", encoding="utf-8", newline="\n"
        )
        require_failure(run(fixture), "C6C9_WEAKENING_TARGET_EXISTS")

    print(
        "STEP8B24_C6C9_WEAKENING_SELFTEST_OK positive=pass "
        "source_tamper=fail_closed audit_scope=fail_closed "
        "missing_prerequisite=fail_closed target_collision=fail_closed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
