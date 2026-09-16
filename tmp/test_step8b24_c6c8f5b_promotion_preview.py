#!/usr/bin/env python3
"""Synthetic fail-closed tests for the C6c.8 f5b promotion preview."""

from __future__ import annotations

import hashlib
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = "audit_step8b24_c6c8f5b_promotion_preview.py"
PATH_LIST = "C6C8F5B-FULL-SCRATCH-PATHS.txt"
NEW_SOURCE = (
    "BalabanCMP99Eq335PhysicalLocalizedRetainedTowerOfSourceRegion.draft.lean"
)
NEW_AUDIT = (
    "BalabanCMP99Eq335PhysicalLocalizedRetainedTowerOfSourceRegionAudit.draft.lean"
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def listed_paths(root: Path) -> list[str]:
    return [
        line.strip()
        for line in (root / "tmp" / PATH_LIST).read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]


def fixture_at(parent: Path) -> Path:
    fixture = parent / "repo"
    (fixture / "tmp").mkdir(parents=True)
    (fixture / "YangMills/RG").mkdir(parents=True)
    shutil.copyfile(ROOT / "tmp" / PATH_LIST, fixture / "tmp" / PATH_LIST)
    shutil.copyfile(ROOT / "tmp" / SCRIPT, fixture / "tmp" / SCRIPT)
    for relative in listed_paths(ROOT):
        target = fixture / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / relative, target)
    return fixture


def run(fixture: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, f"tmp/{SCRIPT}"], cwd=fixture, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
    )


def require_failure(result: subprocess.CompletedProcess[str], token: str) -> None:
    if result.returncode == 0 or token not in result.stdout:
        raise SystemExit(
            f"C6C8F5B_SELFTEST_EXPECTED_FAILURE={token}\n{result.stdout}"
        )


def repin(fixture: Path) -> None:
    script = fixture / "tmp" / SCRIPT
    text = script.read_text(encoding="utf-8")
    paths = listed_paths(fixture)
    raw_lines: list[str] = []
    promoted_lines: list[str] = []
    for relative in paths:
        data = (fixture / relative).read_bytes()
        raw_lines.append(f"{sha256(data)}  {relative}\n")
        target = "YangMills/RG/" + Path(relative).name.replace(
            ".draft.lean", ".lean"
        )
        promoted_lines.append(
            f"{sha256(data.replace(b'\r\n', b'\n'))}  {target}\n"
        )
    replacements = {
        "PATH_LIST_SHA256": sha256((fixture / "tmp" / PATH_LIST).read_bytes()),
        "RAW_AGGREGATE_SHA256": sha256("".join(raw_lines).encode()),
        "PROMOTED_MANIFEST_SHA256": sha256("".join(promoted_lines).encode()),
        "NEW_SOURCE_SHA256": sha256((fixture / "tmp" / NEW_SOURCE).read_bytes()),
        "NEW_AUDIT_SHA256": sha256((fixture / "tmp" / NEW_AUDIT).read_bytes()),
    }
    for name, value in replacements.items():
        text, count = re.subn(
            rf'(?m)^{name} = "[0-9A-F]+"$', f'{name} = "{value}"', text
        )
        if count != 1:
            raise SystemExit(f"C6C8F5B_SELFTEST_REPIN_SCOPE={name}/{count}")
    script.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="c6c8-f5b-") as directory:
        base = Path(directory)

        fixture = fixture_at(base / "positive")
        result = run(fixture)
        if result.returncode != 0 or "C6C8F5B_PROMOTION_PREVIEW_OK" not in result.stdout:
            raise SystemExit("C6C8F5B_SELFTEST_POSITIVE_FAILED\n" + result.stdout)

        fixture = fixture_at(base / "raw-tamper")
        source = fixture / "tmp" / NEW_SOURCE
        source.write_bytes(source.read_bytes() + b"\n")
        require_failure(run(fixture), "C6C8F5B_RAW_AGGREGATE_HASH_MISMATCH")

        fixture = fixture_at(base / "path-tamper")
        path_list = fixture / "tmp" / PATH_LIST
        path_list.write_bytes(path_list.read_bytes() + b"\n")
        require_failure(run(fixture), "C6C8F5B_PATH_LIST_HASH_MISMATCH")

        fixture = fixture_at(base / "semantic-tamper")
        source = fixture / "tmp" / NEW_SOURCE
        source.write_text(
            source.read_text(encoding="utf-8").replace(
                "retainedFineReadCarrierInsideRegularCube W.cube D regions",
                "REMOVED_SOURCE_DICTIONARY_MECHANISM",
            ),
            encoding="utf-8", newline="\n",
        )
        repin(fixture)
        require_failure(run(fixture), "C6C8F5B_REQUIRED_MECHANISM_MISSING")

        fixture = fixture_at(base / "audit-scope")
        audit = fixture / "tmp" / NEW_AUDIT
        audit.write_text(
            audit.read_text(encoding="utf-8").replace(
                "#print axioms", "-- removed", 1
            ),
            encoding="utf-8", newline="\n",
        )
        repin(fixture)
        require_failure(run(fixture), "C6C8F5B_AUDIT_READOUT_MISMATCH")

        fixture = fixture_at(base / "marker-scope")
        source = fixture / "tmp" / NEW_SOURCE
        source.write_text(
            source.read_text(encoding="utf-8").replace(
                "PRE-VALIDATION:", "UNMARKED:", 1
            ),
            encoding="utf-8", newline="\n",
        )
        repin(fixture)
        require_failure(run(fixture), "C6C8F5B_PREVALIDATION_COUNT")

        fixture = fixture_at(base / "collision")
        collision = (
            fixture / "YangMills/RG/" /
            NEW_SOURCE.replace(".draft.lean", ".lean")
        )
        collision.write_text("-- collision\n", encoding="utf-8", newline="\n")
        require_failure(run(fixture), "C6C8F5B_TARGET_EXISTS")

    print(
        "STEP8B24_C6C8F5B_PROMOTION_SELFTEST_OK positive=pass "
        "raw_tamper=fail_closed path_tamper=fail_closed "
        "semantic_tamper=fail_closed audit_scope=fail_closed "
        "marker_scope=fail_closed target_collision=fail_closed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
