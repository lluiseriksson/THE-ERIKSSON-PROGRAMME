#!/usr/bin/env python3
"""Synthetic positive/tamper tests for the C6c.3 promotion preview."""

from __future__ import annotations

import shutil
import subprocess
import sys
import tempfile
import hashlib
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PAIR = (
    "BalabanCMP96Eq240SourceSeparatedSignedCutoffLaplacian.lean",
    "BalabanCMP96Eq240SourceSeparatedSignedCutoffLaplacianAudit.lean",
)
SCRIPT = "audit_step8b24_c6c3_promotion_preview.py"


def run(fixture: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, f"tmp/{SCRIPT}"],
        cwd=fixture,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )


def fixture_at(parent: Path) -> Path:
    fixture = parent / "repo"
    (fixture / "tmp").mkdir(parents=True)
    (fixture / "YangMills/RG").mkdir(parents=True)
    for name in (*PAIR, SCRIPT):
        shutil.copyfile(ROOT / "tmp" / name, fixture / "tmp" / name)
    (fixture / "YangMills/RG/BalabanCMP99SourceSeparatedSignedCutoffLaplacian.lean").write_text(
        "-- sealed external prerequisite fixture\n", encoding="utf-8", newline="\n"
    )
    return fixture


def require_failure(result: subprocess.CompletedProcess[str], token: str) -> None:
    if result.returncode == 0 or token not in result.stdout:
        raise SystemExit(f"C6C3_PREVIEW_SELFTEST_EXPECTED_FAILURE={token}\n{result.stdout}")


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="c6c3-preview-") as directory:
        base = Path(directory)

        fixture = fixture_at(base / "positive")
        positive = run(fixture)
        if positive.returncode != 0 or "C6C3_PROMOTION_PREVIEW_OK" not in positive.stdout:
            raise SystemExit("C6C3_PREVIEW_SELFTEST_POSITIVE_FAILED\n" + positive.stdout)

        fixture = fixture_at(base / "source-tamper")
        source = fixture / "tmp" / PAIR[0]
        source.write_bytes(source.read_bytes() + b"\n")
        require_failure(run(fixture), "C6C3_RAW_HASH_MISMATCH")

        fixture = fixture_at(base / "audit-scope-tamper")
        audit = fixture / "tmp" / PAIR[1]
        changed = audit.read_text(encoding="utf-8").replace(
                "#print axioms YangMills.RG."
                "norm_cmp96Eq240SourceSeparatedSignedCutoffLaplacianKTerm_le\n",
                "",
        )
        audit.write_text(changed, encoding="utf-8", newline="\n")
        script = fixture / "tmp" / SCRIPT
        script_text = script.read_text(encoding="utf-8")
        script_text = script_text.replace(
            "A7D9438FAD9D637B6C56D7492EA2231A7883A6F71C149D5B6CEB58DF79650805",
            hashlib.sha256(audit.read_bytes()).hexdigest().upper(),
        )
        script.write_text(script_text, encoding="utf-8", newline="\n")
        require_failure(run(fixture), "C6C3_AUDIT_READOUT_SCOPE")

        fixture = fixture_at(base / "missing-prerequisite")
        (fixture / "YangMills/RG/BalabanCMP99SourceSeparatedSignedCutoffLaplacian.lean").unlink()
        require_failure(run(fixture), "C6C3_SOURCE_IMPORT_UNRESOLVED")

        fixture = fixture_at(base / "collision")
        target = fixture / "YangMills/RG" / PAIR[0]
        target.write_text("-- collision\n", encoding="utf-8", newline="\n")
        require_failure(run(fixture), "C6C3_PROMOTION_TARGET_EXISTS")

    print(
        "STEP8B24_C6C3_PROMOTION_PREVIEW_SELFTEST_OK "
        "positive=pass source_tamper=fail_closed audit_scope=fail_closed "
        "missing_prerequisite=fail_closed target_collision=fail_closed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
