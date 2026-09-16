#!/usr/bin/env python3
"""Synthetic tamper tests for the C6c.9 common-amplitude preview."""

from __future__ import annotations

import hashlib
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = "audit_step8b24_c6c9_common_amplitude_preview.py"
PAIR = (
    "BalabanCMP99Eq342CommonAmplitude.draft.lean",
    "BalabanCMP99Eq342CommonAmplitudeAudit.draft.lean",
)


def fixture_at(parent: Path) -> Path:
    fixture = parent / "repo"
    (fixture / "tmp").mkdir(parents=True)
    (fixture / "YangMills/RG").mkdir(parents=True)
    for name in (*PAIR, SCRIPT):
        shutil.copyfile(ROOT / "tmp" / name, fixture / "tmp" / name)
    return fixture


def run(fixture: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, f"tmp/{SCRIPT}"], cwd=fixture, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
    )


def require_failure(result: subprocess.CompletedProcess[str], token: str) -> None:
    if result.returncode == 0 or token not in result.stdout:
        raise SystemExit(f"C6C9_COMMON_SELFTEST_EXPECTED_FAILURE={token}\n{result.stdout}")


def rehash_script(fixture: Path, old: str, changed: Path) -> None:
    script = fixture / "tmp" / SCRIPT
    replacement = hashlib.sha256(changed.read_bytes()).hexdigest().upper()
    script.write_text(
        script.read_text(encoding="utf-8").replace(old, replacement),
        encoding="utf-8", newline="\n",
    )


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="c6c9-common-") as directory:
        base = Path(directory)

        fixture = fixture_at(base / "positive")
        positive = run(fixture)
        if positive.returncode != 0 or "C6C9_COMMON_AMPLITUDE_PREVIEW_OK" not in positive.stdout:
            raise SystemExit("C6C9_COMMON_SELFTEST_POSITIVE_FAILED\n" + positive.stdout)

        fixture = fixture_at(base / "source-tamper")
        source = fixture / "tmp" / PAIR[0]
        source.write_bytes(source.read_bytes() + b"\n")
        require_failure(run(fixture), "C6C9_COMMON_RAW_HASH_MISMATCH")

        fixture = fixture_at(base / "formula-tamper")
        source = fixture / "tmp" / PAIR[0]
        source.write_text(
            source.read_text(encoding="utf-8").replace(
                "1 + Avalue + Aleft + Aright + Alaplacian",
                "Avalue + Aleft + Aright + Alaplacian",
            ), encoding="utf-8", newline="\n",
        )
        rehash_script(
            fixture,
            "4A380139EB1A290C1840A09C3C69AC5A939C6E0985E46565D24833D458F13FA6",
            source,
        )
        require_failure(run(fixture), "C6C9_COMMON_SEMANTIC_TOKEN_MISSING")

        fixture = fixture_at(base / "audit-scope")
        audit = fixture / "tmp" / PAIR[1]
        audit.write_text(
            audit.read_text(encoding="utf-8").replace(
                "#print axioms YangMills.RG.le_cmp99Eq342CommonAmplitude_right\n", ""
            ), encoding="utf-8", newline="\n",
        )
        rehash_script(
            fixture,
            "9DC5B31AD39AAB31D9A1936DAEBD81EB238D80407A1FA19978FA3DF1947F039B",
            audit,
        )
        require_failure(run(fixture), "C6C9_COMMON_AUDIT_READOUT_SCOPE")

        fixture = fixture_at(base / "collision")
        (fixture / "YangMills/RG/BalabanCMP99Eq342CommonAmplitude.lean").write_text(
            "-- collision\n", encoding="utf-8", newline="\n"
        )
        require_failure(run(fixture), "C6C9_COMMON_TARGET_EXISTS")

    print(
        "STEP8B24_C6C9_COMMON_AMPLITUDE_SELFTEST_OK positive=pass "
        "source_tamper=fail_closed formula_tamper=fail_closed "
        "audit_scope=fail_closed target_collision=fail_closed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
