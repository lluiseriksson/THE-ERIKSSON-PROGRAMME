#!/usr/bin/env python3
"""Fail-closed mechanical promotion of Step 8b.24 C6c.1 H1--H2d3."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import runpy
import subprocess


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
OVERLAY = TMP / "step8b24-c6c1-h1-h2b-overlay"
MANIFEST = TMP / "STEP8B24-C6C1-H1-H2B-OVERLAY-MANIFEST.json"
PREPARE = runpy.run_path(
    str(TMP / "prepare_step8b24_c6c1_h1_h2b_overlay.py")
)
EXPECTED_MANIFEST_SHA256 = (
    "5AABA4F160BC1FA0FB8BB58A81306275FB3A76B968F9F26411828E8AD482A6EC"
)
PREREQUISITE_LISTS: tuple[tuple[Path, str, int], ...] = (
    (
        TMP / "STEP8B24-ALL-PATHS.txt",
        "04D159C779790BBC9E7B5CB6BEB98EE1309245B252AD177E7D97C359819EE63B",
        78,
    ),
    (
        TMP / "STEP8B24-C6C1-PREFIX-PATHS.txt",
        "C8A9F71F0723F914E0380A9A8038AB72510FCE602C1291995FCA4D5EF4A2E938",
        8,
    ),
    (
        TMP / "STEP8B24-C6C1-D4-PATHS.txt",
        "D00253F5ADC61A56214DEDEA1D84115ECFD3CFF5B628AF7472084454B0D7F36A",
        6,
    ),
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


def target_of_draft_row(raw: str) -> Path:
    prefix = "tmp/"
    suffix = ".draft.lean"
    if not raw.startswith(prefix) or not raw.endswith(suffix):
        raise SystemExit(f"BAD_PREREQUISITE_DRAFT_PATH={raw}")
    stem = raw.removeprefix(prefix).removesuffix(suffix)
    return Path("YangMills") / "RG" / f"{stem}.lean"


def require_sealed_prerequisites() -> None:
    rows: list[Path] = []
    for path_list, expected_digest, expected_count in PREREQUISITE_LISTS:
        measured_digest = sha256(path_list.read_bytes())
        if measured_digest != expected_digest:
            raise SystemExit(
                f"HOLDER_PREREQUISITE_LIST_DRIFT={path_list.name}/{measured_digest}"
            )
        raw_rows = [
            raw.strip()
            for raw in path_list.read_text(encoding="utf-8-sig").splitlines()
            if raw.strip() and not raw.lstrip().startswith("#")
        ]
        if len(raw_rows) != expected_count:
            raise SystemExit(
                f"HOLDER_PREREQUISITE_LIST_COUNT={path_list.name}/{len(raw_rows)}"
            )
        rows.extend(target_of_draft_row(raw) for raw in raw_rows)
    if len(rows) != 92 or len(rows) != len(set(rows)):
        raise SystemExit(f"HOLDER_PREREQUISITE_SCOPE_MISMATCH={len(rows)}")

    core = (ROOT / "YangMillsCore.lean").read_text(encoding="utf-8")
    for relative in rows:
        target = ROOT / relative
        if not target.is_file():
            raise SystemExit(f"HOLDER_PREREQUISITE_MISSING={relative.as_posix()}")
        text = target.read_text(encoding="utf-8")
        if "PRE-VALIDATION:" in text:
            raise SystemExit(f"HOLDER_PREREQUISITE_NOT_SEALED={relative.as_posix()}")
        if relative.name.endswith("Audit.lean"):
            module = relative.with_suffix("").as_posix().replace("/", ".")
            if f"import {module}" not in core:
                raise SystemExit(f"HOLDER_PREREQUISITE_NOT_IN_CORE={module}")


def promotion_plan() -> list[tuple[Path, bytes]]:
    require_sealed_prerequisites()
    PREPARE["main"]()
    if sha256(MANIFEST.read_bytes()) != EXPECTED_MANIFEST_SHA256:
        raise SystemExit(
            "HOLDER_MANIFEST_DRIFT=" + sha256(MANIFEST.read_bytes())
        )
    payload = json.loads(MANIFEST.read_text(encoding="utf-8"))
    records: list[dict[str, object]] = payload["files"]
    if (
        payload.get("status") != "PRE-VALIDATION"
        or payload.get("compiler_verified") is not False
        or payload.get("declarations") != 30
        or payload.get("axiom_prints") != 30
        or payload.get("internal_import_edges") != 19
        or len(records) != 18
    ):
        raise SystemExit("HOLDER_MANIFEST_SEMANTIC_MISMATCH")

    result: list[tuple[Path, bytes]] = []
    core = (ROOT / "YangMillsCore.lean").read_text(encoding="utf-8")
    for record in records:
        relative = Path(str(record["path"]))
        source = OVERLAY / relative
        target = ROOT / relative
        if not source.is_file():
            raise SystemExit(f"HOLDER_OVERLAY_FILE_MISSING={relative.as_posix()}")
        content = source.read_bytes()
        if sha256(content) != record["sha256"]:
            raise SystemExit(f"HOLDER_OVERLAY_BLOB_DRIFT={relative.as_posix()}")
        if content.decode("utf-8").count("PRE-VALIDATION:") != 1:
            raise SystemExit(f"HOLDER_PRE_MARKER_COUNT={relative.as_posix()}")
        if target.exists():
            raise SystemExit(f"HOLDER_TARGET_ALREADY_EXISTS={relative.as_posix()}")
        if relative.name.endswith("Audit.lean"):
            module = relative.with_suffix("").as_posix().replace("/", ".")
            if f"import {module}" in core:
                raise SystemExit(f"HOLDER_AUDIT_PREMATURELY_IN_CORE={module}")
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
            "STEP8B24_C6C1_HOLDER_PROMOTION_DRY_RUN_OK "
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
        "STEP8B24_C6C1_HOLDER_PROMOTION_WRITE_OK "
        f"base_head={actual} new_files={len(promotion)} "
        f"manifest={EXPECTED_MANIFEST_SHA256}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
