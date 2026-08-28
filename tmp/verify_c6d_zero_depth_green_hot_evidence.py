#!/usr/bin/env python3
"""Fail-closed verifier for the depth-zero Green hot diagnostic."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path, PurePosixPath
import re
import tarfile


SOURCE_SHA = "be4e66a1262e132cf0721fb0f3768e9e884bb3ad"
ROOT = "hrpoly-c6d-zero-depth-green-hot-evidence"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_AXIOM_HEADERS = 6
EXPECTED_PATHS = {
    f"{ROOT}/zero_depth_green_fetch_exact_sha.stdout",
    f"{ROOT}/zero_depth_green_checkout_exact_sha.stdout",
    f"{ROOT}/zero_depth_green_verify_head.stdout",
    f"{ROOT}/zero_depth_green_text_guard_c6d-full-companion-zero-depth-draft-paths.stdout",
    f"{ROOT}/zero_depth_green_text_guard_c6d-full-companion-zero-depth-green-draft-paths.stdout",
    f"{ROOT}/zero_depth_green_source.stdout",
    f"{ROOT}/zero_depth_green_audit.stdout",
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest().upper()


def safe_regular_members(archive: tarfile.TarFile) -> dict[str, bytes]:
    result: dict[str, bytes] = {}
    for member in archive.getmembers():
        path = PurePosixPath(member.name)
        if path.is_absolute() or ".." in path.parts:
            raise RuntimeError(f"UNSAFE_ARCHIVE_MEMBER={member.name}")
        if member.isdir():
            continue
        if not member.isfile():
            raise RuntimeError(f"NONREGULAR_ARCHIVE_MEMBER={member.name}")
        extracted = archive.extractfile(member)
        if extracted is None:
            raise RuntimeError(f"UNREADABLE_ARCHIVE_MEMBER={member.name}")
        if member.name in result:
            raise RuntimeError(f"DUPLICATE_ARCHIVE_MEMBER={member.name}")
        result[member.name] = extracted.read()
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("archive", type=Path)
    args = parser.parse_args()
    archive_path = args.archive.resolve()
    if not archive_path.is_file():
        raise RuntimeError(f"ARCHIVE_NOT_FOUND={archive_path}")
    with tarfile.open(archive_path, "r:gz") as archive:
        members = safe_regular_members(archive)
    actual = set(members)
    missing = sorted(EXPECTED_PATHS - actual)
    unexpected = sorted(actual - EXPECTED_PATHS)
    if missing:
        raise RuntimeError(f"MISSING_ARCHIVE_MEMBERS={missing!r}")
    if unexpected:
        raise RuntimeError(f"UNEXPECTED_ARCHIVE_MEMBERS={unexpected!r}")
    head = members[f"{ROOT}/zero_depth_green_verify_head.stdout"].decode().strip()
    if head != SOURCE_SHA:
        raise RuntimeError(f"SOURCE_SHA={head!r} EXPECTED={SOURCE_SHA!r}")
    for guard in (
        f"{ROOT}/zero_depth_green_text_guard_c6d-full-companion-zero-depth-draft-paths.stdout",
        f"{ROOT}/zero_depth_green_text_guard_c6d-full-companion-zero-depth-green-draft-paths.stdout",
    ):
        if "LEAN_OVERLAY_TEXT_OK" not in members[guard].decode("utf-8"):
            raise RuntimeError(f"TEXT_GUARD_NOT_GREEN={guard}")
    audit = members[f"{ROOT}/zero_depth_green_audit.stdout"].decode("utf-8")
    dependency_blocks = re.findall(
        r"depends on axioms:\s*\[(.*?)\]", audit, flags=re.DOTALL
    )
    pure_count = audit.count("does not depend on any axioms")
    actual_headers = len(dependency_blocks) + pure_count
    if actual_headers != EXPECTED_AXIOM_HEADERS:
        raise RuntimeError(
            f"AXIOM_HEADER_COUNT={actual_headers} EXPECTED={EXPECTED_AXIOM_HEADERS}"
        )
    for block in dependency_blocks:
        names = {name.strip() for name in block.replace("\n", " ").split(",")}
        forbidden = sorted(name for name in names if name not in ALLOWED_AXIOMS)
        if forbidden:
            raise RuntimeError(f"FORBIDDEN_AXIOMS={forbidden!r}")
    for forbidden in ("sorryAx", "ofReduceBool"):
        if forbidden in audit:
            raise RuntimeError(f"FORBIDDEN_AXIOM_TOKEN={forbidden}")
    print("C6D_ZERO_DEPTH_GREEN_HOT_EVIDENCE_OK")
    print(f"SOURCE_SHA={SOURCE_SHA}")
    print(f"ARCHIVE_MEMBERS={len(members)}")
    print(f"AXIOM_HEADERS={actual_headers}")
    print(f"ARCHIVE_SHA256={sha256(archive_path)}")
    print("CLASSIFICATION=HOT_DIAGNOSTIC_ONLY")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
