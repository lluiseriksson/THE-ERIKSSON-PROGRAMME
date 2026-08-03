#!/usr/bin/env python3
"""Build the deterministic 2026-08-01 supersession-replacement hand-off."""

from __future__ import annotations

import hashlib
import zipfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / "docs" / "publication-audit"
OUT = ROOT / "output" / "publication-audit"
RELEASES = OUT / "releases"
FINAL = OUT / "final"
PACKAGES = (
    "2512.0073-v2",
    "2601.0047-v3",
    "2607.0035-v2",
    "2607.0023-v2",
)
FIXED_TIME = (2026, 8, 1, 0, 0, 0)
MANIFEST_NAME = "SUPERSESSION-REPLACEMENTS-20260801-MANIFEST.txt"
ZIP_NAME = "SUPERSESSION-REPLACEMENTS-20260801.zip"
SHA_NAME = "SUPERSESSION-REPLACEMENTS-20260801-ZIP-SHA256.txt"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def selected_files() -> list[tuple[Path, str]]:
    files: list[tuple[Path, str]] = []
    for name in (
        "SUBMISSION-STATUS-20260801.md",
        "PAPER-AUDIT-LEDGER.md",
        "SUPERSESSION-MATRIX.md",
        "OWNER-SUBMISSION-CHECKLIST.md",
        "REVIEW-PENDING.md",
        "SUPERSESSION-REPLACEMENT-PREFLIGHT.md",
        "SUPERSESSION-REPLACEMENT-PREFLIGHT.json",
    ):
        path = DOCS / name
        if not path.is_file():
            raise FileNotFoundError(path)
        files.append((path, f"docs/{name}"))
    for package in PACKAGES:
        for suffix in (".zip", "-ZIP-SHA256.txt"):
            path = RELEASES / f"{package}{suffix}"
            if not path.is_file():
                raise FileNotFoundError(path)
            files.append((path, f"packages/{path.name}"))
        manifests = sorted(RELEASES.glob(f"{package}-MANIFEST*.txt"))
        if len(manifests) != 1:
            raise RuntimeError(f"expected one manifest for {package}: {manifests}")
        files.append((manifests[0], f"packages/{manifests[0].name}"))
    for name in (
        "build_publication_audit_release.py",
        "audit_supersession_replacement_releases.py",
        "build_supersession_replacement_bundle.py",
    ):
        path = ROOT / "scripts" / name
        if not path.is_file():
            raise FileNotFoundError(path)
        files.append((path, f"scripts/{name}"))
    return sorted(files, key=lambda item: item[1])


def manifest_bytes(files: list[tuple[Path, str]]) -> bytes:
    lines = [
        "ERIKSSON SUPERSESSION REPLACEMENTS — OWNER HAND-OFF",
        "AUDIT_DATE: 2026-08-01",
        "PACKAGE_COUNT: 4",
        "OWNER_ACTION: NO AUTOMATED SUBMISSION PERFORMED",
        "MANIFEST_SCOPE: payload files; this manifest excludes itself by definition",
        "",
        "SHA256  BYTES  PATH",
    ]
    for path, arcname in files:
        lines.append(f"{sha256(path)}  {path.stat().st_size}  {arcname}")
    lines.extend(("", f"PAYLOAD_FILE_COUNT: {len(files)}", ""))
    return "\n".join(lines).encode("utf-8")


def info(name: str) -> zipfile.ZipInfo:
    item = zipfile.ZipInfo(name, FIXED_TIME)
    item.compress_type = zipfile.ZIP_DEFLATED
    item.create_system = 3
    item.external_attr = 0o100644 << 16
    return item


def main() -> int:
    files = selected_files()
    manifest = manifest_bytes(files)
    FINAL.mkdir(parents=True, exist_ok=True)
    manifest_path = FINAL / MANIFEST_NAME
    zip_path = FINAL / ZIP_NAME
    sha_path = FINAL / SHA_NAME
    manifest_path.write_bytes(manifest)
    with zipfile.ZipFile(zip_path, "w", compresslevel=9) as archive:
        for path, arcname in files:
            archive.writestr(info(arcname), path.read_bytes())
        archive.writestr(info(MANIFEST_NAME), manifest)
    with zipfile.ZipFile(zip_path) as archive:
        if archive.read(MANIFEST_NAME) != manifest_path.read_bytes():
            raise RuntimeError("internal and external bundle manifests differ")
        for path, arcname in files:
            if hashlib.sha256(archive.read(arcname)).hexdigest() != sha256(path):
                raise RuntimeError(f"bundle member mismatch: {arcname}")
    digest = sha256(zip_path)
    sha_path.write_text(f"{digest}  {ZIP_NAME}\n", encoding="ascii", newline="\n")
    print(f"PASS {ZIP_NAME} {digest} ({zip_path.stat().st_size} bytes)")
    print(f"PASS manifest internal=external SHA256 {hashlib.sha256(manifest).hexdigest()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
