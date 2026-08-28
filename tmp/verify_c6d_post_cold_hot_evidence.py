#!/usr/bin/env python3
"""Fail-closed verifier for the three retained-runtime C6d hot queues.

The verified archive is diagnostic evidence only.  It can authorize promotion
of the exact PRE-VALIDATION sources to a later cold queue, but it is not cold
seal evidence and cannot move the terminal counters.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path, PurePosixPath
import re
import tarfile


FULL_SOURCE_SHA = "ec4db69a54e0f47189940086476edf4c47a39abe"
AMBIENT_SOURCE_SHA = "228ff08ded55d87956266e9fca2dca0f9dce1796"
ZERO_SOURCE_SHA = "4cd9364e64fa039878ccfcb20a1dbb64b02cb5f5"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

FULL_MODULES = [
    ("BalabanCMP99RegionalDirichletGaugePrecisionCompression", 2),
    ("BalabanCMP99SourceActiveRegionFullCompanion", 5),
    ("BalabanCMP99SourceGeneratedMassCompression", 3),
    ("BalabanCMP99SourceGeneratedPhysicalPrecisionCompression", 3),
    ("BalabanCMP99SourceActiveRegionFullCompanionPrecision", 6),
    ("BalabanCMP99SourceActiveRegionFullCompanionAmbientPrecision", 6),
]

AMBIENT_MODULES = [
    ("BalabanCMP99ActiveGaugeRegionReindex", 10),
    ("BalabanCMP99Eq360C6dSourceAmbientBaselinePrecision", 7),
    ("BalabanCMP99ActiveGaugeRegionReindexGreen", 4),
]

FULL_ROOT = "hrpoly-c6d-full-companion-hot-evidence"
AMBIENT_ROOT = "hrpoly-c6d-ambient-region-hot-evidence"
ZERO_ROOT = "hrpoly-c6d-zero-depth-hot-evidence"


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


def audit_axioms(payload: bytes, expected: int, label: str) -> None:
    text = payload.decode("utf-8")
    dependency_blocks = re.findall(
        r"depends on axioms:\s*\[(.*?)\]", text, flags=re.DOTALL
    )
    pure_count = text.count("does not depend on any axioms")
    actual = len(dependency_blocks) + pure_count
    if actual != expected:
        raise RuntimeError(
            f"AXIOM_HEADER_COUNT_{label}={actual} EXPECTED={expected}"
        )
    for block in dependency_blocks:
        names = {name.strip() for name in block.replace("\n", " ").split(",")}
        forbidden = sorted(name for name in names if name not in ALLOWED_AXIOMS)
        if forbidden:
            raise RuntimeError(f"FORBIDDEN_AXIOMS_{label}={forbidden!r}")
    for forbidden in ("sorryAx", "ofReduceBool"):
        if forbidden in text:
            raise RuntimeError(f"FORBIDDEN_AXIOM_TOKEN_{label}={forbidden}")


def full_expected_paths() -> set[str]:
    paths = {
        f"{FULL_ROOT}/hot_fetch_exact_sha.stdout",
        f"{FULL_ROOT}/hot_checkout_exact_sha.stdout",
        f"{FULL_ROOT}/hot_verify_head.stdout",
        f"{FULL_ROOT}/hot_text_guard.stdout",
    }
    for index, (module, _) in enumerate(FULL_MODULES, start=1):
        for suffix in ("", "Audit"):
            target = module + suffix
            paths.add(f"{FULL_ROOT}/hot_{index:02d}_{target.lower()}.stdout")
    return paths


def ambient_expected_paths() -> set[str]:
    paths = {
        f"{AMBIENT_ROOT}/ambient_region_fetch_exact_sha.stdout",
        f"{AMBIENT_ROOT}/ambient_region_checkout_exact_sha.stdout",
        f"{AMBIENT_ROOT}/ambient_region_verify_head.stdout",
        f"{AMBIENT_ROOT}/text_guard_c6d-active-region-reindex-draft-paths.stdout",
        f"{AMBIENT_ROOT}/text_guard_c6d-ambient-baseline-draft-paths.stdout",
        f"{AMBIENT_ROOT}/text_guard_c6d-active-region-reindex-green-draft-paths.stdout",
    }
    for index, (module, _) in enumerate(AMBIENT_MODULES, start=1):
        stem = f"{AMBIENT_ROOT}/ambient_region_{index:02d}_{module.lower()}"
        paths.add(stem + "_source.stdout")
        paths.add(stem + "_audit.stdout")
    return paths


def zero_expected_paths() -> set[str]:
    return {
        f"{ZERO_ROOT}/zero_depth_fetch_exact_sha.stdout",
        f"{ZERO_ROOT}/zero_depth_checkout_exact_sha.stdout",
        f"{ZERO_ROOT}/zero_depth_verify_head.stdout",
        f"{ZERO_ROOT}/zero_depth_text_guard.stdout",
        f"{ZERO_ROOT}/zero_depth_source.stdout",
        f"{ZERO_ROOT}/zero_depth_audit.stdout",
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("archive", type=Path)
    args = parser.parse_args()
    archive_path = args.archive.resolve()
    if not archive_path.is_file():
        raise RuntimeError(f"ARCHIVE_NOT_FOUND={archive_path}")

    with tarfile.open(archive_path, "r:gz") as archive:
        members = safe_regular_members(archive)

    expected = full_expected_paths() | ambient_expected_paths() | zero_expected_paths()
    actual = set(members)
    missing = sorted(expected - actual)
    unexpected = sorted(actual - expected)
    if missing:
        raise RuntimeError(f"MISSING_ARCHIVE_MEMBERS={missing!r}")
    if unexpected:
        raise RuntimeError(f"UNEXPECTED_ARCHIVE_MEMBERS={unexpected!r}")

    full_head = members[f"{FULL_ROOT}/hot_verify_head.stdout"].decode().strip()
    if full_head != FULL_SOURCE_SHA:
        raise RuntimeError(
            f"FULL_SOURCE_SHA={full_head!r} EXPECTED={FULL_SOURCE_SHA!r}"
        )
    ambient_head = members[
        f"{AMBIENT_ROOT}/ambient_region_verify_head.stdout"
    ].decode().strip()
    if ambient_head != AMBIENT_SOURCE_SHA:
        raise RuntimeError(
            f"AMBIENT_SOURCE_SHA={ambient_head!r} EXPECTED={AMBIENT_SOURCE_SHA!r}"
        )
    zero_head = members[f"{ZERO_ROOT}/zero_depth_verify_head.stdout"].decode().strip()
    if zero_head != ZERO_SOURCE_SHA:
        raise RuntimeError(
            f"ZERO_SOURCE_SHA={zero_head!r} EXPECTED={ZERO_SOURCE_SHA!r}"
        )

    for index, (module, count) in enumerate(FULL_MODULES, start=1):
        path = f"{FULL_ROOT}/hot_{index:02d}_{(module + 'Audit').lower()}.stdout"
        audit_axioms(members[path], count, module)
    for index, (module, count) in enumerate(AMBIENT_MODULES, start=1):
        path = f"{AMBIENT_ROOT}/ambient_region_{index:02d}_{module.lower()}_audit.stdout"
        audit_axioms(members[path], count, module)
    audit_axioms(
        members[f"{ZERO_ROOT}/zero_depth_audit.stdout"],
        3,
        "BalabanCMP99SourceActiveRegionFullCompanionZeroDepth",
    )

    for guard in (
        f"{FULL_ROOT}/hot_text_guard.stdout",
        f"{AMBIENT_ROOT}/text_guard_c6d-active-region-reindex-draft-paths.stdout",
        f"{AMBIENT_ROOT}/text_guard_c6d-ambient-baseline-draft-paths.stdout",
        f"{AMBIENT_ROOT}/text_guard_c6d-active-region-reindex-green-draft-paths.stdout",
        f"{ZERO_ROOT}/zero_depth_text_guard.stdout",
    ):
        if "LEAN_OVERLAY_TEXT_OK" not in members[guard].decode("utf-8"):
            raise RuntimeError(f"TEXT_GUARD_NOT_GREEN={guard}")

    print("C6D_POST_COLD_HOT_EVIDENCE_OK")
    print(f"FULL_SOURCE_SHA={FULL_SOURCE_SHA}")
    print(f"AMBIENT_SOURCE_SHA={AMBIENT_SOURCE_SHA}")
    print(f"ZERO_SOURCE_SHA={ZERO_SOURCE_SHA}")
    print(f"ARCHIVE_MEMBERS={len(members)}")
    print(f"AXIOM_HEADERS={sum(n for _, n in FULL_MODULES + AMBIENT_MODULES) + 3}")
    print(f"ARCHIVE_SHA256={sha256(archive_path)}")
    print("CLASSIFICATION=HOT_DIAGNOSTIC_ONLY")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
