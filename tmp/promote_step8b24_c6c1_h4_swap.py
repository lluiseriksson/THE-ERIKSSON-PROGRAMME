#!/usr/bin/env python3
"""Fail-closed promotion of the H4a/H4b PRE-VALIDATION overlay."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
OVERLAY = TMP / "step8b24-c6c1-h4-swap-overlay"
MANIFEST = TMP / "STEP8B24-C6C1-H4-SWAP-OVERLAY-MANIFEST.json"
EXPECTED_MANIFEST_SHA256 = (
    "A8EC12904CB695C8EB1258D6FA3B6BB010BD907EBC8F39C3433E9AD5672E0DC9"
)
PREREQUISITES = (
    "BalabanCMP89Eq251ComplexContourPhase",
    "BalabanCMP89Eq251StabilizedEndpointRecombination",
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def git(*args: str) -> str:
    child = subprocess.run(
        ["git", "-c", "safe.directory=*", *args],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        check=False,
    )
    if child.returncode != 0:
        raise SystemExit("GIT_FAIL " + " ".join(args) + "\n" + child.stderr)
    return child.stdout.strip()


def require_prerequisites() -> None:
    core = (ROOT / "YangMillsCore.lean").read_text(encoding="utf-8")
    for module in PREREQUISITES:
        for suffix in (".lean", "Audit.lean"):
            relative = Path("YangMills/RG") / f"{module}{suffix}"
            path = ROOT / relative
            if not path.is_file():
                raise SystemExit(f"H4_SWAP_PREREQUISITE_MISSING={relative.as_posix()}")
            if "PRE-VALIDATION:" in path.read_text(encoding="utf-8"):
                raise SystemExit(f"H4_SWAP_PREREQUISITE_NOT_SEALED={relative.as_posix()}")
        audit_import = f"import YangMills.RG.{module}Audit"
        if audit_import not in core:
            raise SystemExit(f"H4_SWAP_PREREQUISITE_NOT_IN_CORE={audit_import}")


def promotion_plan() -> list[tuple[Path, bytes]]:
    require_prerequisites()
    measured_manifest = sha256(MANIFEST.read_bytes())
    if measured_manifest != EXPECTED_MANIFEST_SHA256:
        raise SystemExit(f"H4_SWAP_MANIFEST_DRIFT={measured_manifest}")
    payload = json.loads(MANIFEST.read_text(encoding="utf-8"))
    records: list[dict[str, object]] = payload["files"]
    if (
        payload.get("status") != "PRE-VALIDATION"
        or payload.get("compiler_verified") is not False
        or payload.get("declarations") != 12
        or payload.get("axiom_prints") != 7
        or payload.get("physical_fine_displacements") != "BOTH_LITERAL"
        or payload.get("source_metric_dictionary") != "OPEN"
        or payload.get("complete_holder_bound") != "OPEN"
        or len(records) != 2
    ):
        raise SystemExit("H4_SWAP_MANIFEST_SEMANTIC_MISMATCH")

    result: list[tuple[Path, bytes]] = []
    for record in records:
        relative = Path(str(record["path"]))
        if relative.parent != Path("YangMills/RG"):
            raise SystemExit(f"H4_SWAP_BAD_TARGET={relative.as_posix()}")
        source = OVERLAY / relative
        target = ROOT / relative
        if not source.is_file():
            raise SystemExit(f"H4_SWAP_OVERLAY_FILE_MISSING={relative.as_posix()}")
        content = source.read_bytes()
        if sha256(content) != record["sha256"]:
            raise SystemExit(f"H4_SWAP_OVERLAY_BLOB_DRIFT={relative.as_posix()}")
        if len(content) != record["bytes"]:
            raise SystemExit(f"H4_SWAP_OVERLAY_SIZE_DRIFT={relative.as_posix()}")
        text = content.decode("utf-8")
        if text.count("PRE-VALIDATION:") != 1:
            raise SystemExit(f"H4_SWAP_PRE_MARKER_COUNT={relative.as_posix()}")
        if any(token in text for token in ("sorry", "admit", "by?", "exact?")):
            raise SystemExit(f"H4_SWAP_FORBIDDEN_PLACEHOLDER={relative.as_posix()}")
        if target.exists():
            raise SystemExit(f"H4_SWAP_TARGET_ALREADY_EXISTS={relative.as_posix()}")
        result.append((target, content))
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--expected-head", required=True)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()

    actual = git("rev-parse", "HEAD")
    if actual != args.expected_head:
        raise SystemExit(f"HEAD_MISMATCH={actual}")
    if subprocess.run(
        ["git", "-c", "safe.directory=*", "diff", "--quiet"], cwd=ROOT
    ).returncode != 0:
        raise SystemExit("TRACKED_WORKTREE_NOT_CLEAN")
    if subprocess.run(
        ["git", "-c", "safe.directory=*", "diff", "--cached", "--quiet"], cwd=ROOT
    ).returncode != 0:
        raise SystemExit("INDEX_NOT_CLEAN")

    promotion = promotion_plan()
    if not args.write:
        print(
            "STEP8B24_C6C1_H4_SWAP_PROMOTION_DRY_RUN_OK "
            f"head={actual} new_files={len(promotion)} "
            f"manifest={EXPECTED_MANIFEST_SHA256}"
        )
        return 0

    for target, content in promotion:
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)
    for target, content in promotion:
        if target.read_bytes() != content:
            raise SystemExit(f"POST_WRITE_BYTE_MISMATCH={target.relative_to(ROOT)}")
    print(
        "STEP8B24_C6C1_H4_SWAP_PROMOTION_WRITE_OK "
        f"base_head={actual} new_files={len(promotion)} "
        f"manifest={EXPECTED_MANIFEST_SHA256}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
