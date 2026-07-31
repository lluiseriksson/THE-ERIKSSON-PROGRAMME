#!/usr/bin/env python3
"""Create the deterministic owner hand-off ZIP for the 2026-07-31 audit."""

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
    "2602.0052-v3",
    "2602.0036-v3",
    "2602.0033-r30",
    "2602.0085-v2",
    "2602.0084-v2",
    "2602.0035-v2",
    "2602.0038-v3",
    "2602.0041-v4",
    "2601.0115-v3",
)
FIXED_TIME = (2026, 7, 31, 0, 0, 0)


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def selected_files() -> list[tuple[Path, str]]:
    required_docs = (
        "PUBLICATION-CENSUS-20260731.md",
        "PUBLICATION-CENSUS-20260731.csv",
        "PUBLICATION-CENSUS-20260731.json",
        "CENSUS-DISCREPANCIES.md",
        "PAPER-AUDIT-LEDGER.md",
        "PAPER-AUDIT-LEDGER.json",
        "CLAIM-DEPENDENCY-GRAPH.md",
        "MACHINE-VERIFICATION-AUDIT.md",
        "SUPERSESSION-MATRIX.md",
        "OWNER-SUBMISSION-CHECKLIST.md",
        "REVIEW-PENDING.md",
        "FINAL-PACKAGE-PREFLIGHT.md",
        "FINAL-PACKAGE-PREFLIGHT.json",
    )
    files: list[tuple[Path, str]] = []
    for name in required_docs:
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
            raise RuntimeError(f"expected one external manifest for {package}, got {manifests}")
        files.append((manifests[0], f"packages/{manifests[0].name}"))
    for name in (
        "generate_publication_audit_census.py",
        "compile_publication_audit.py",
        "render_publication_audit.py",
        "build_publication_audit_release.py",
        "audit_publication_audit_releases.py",
        "build_final_publication_audit_bundle.py",
    ):
        path = ROOT / "scripts" / name
        if not path.is_file():
            raise FileNotFoundError(path)
        files.append((path, f"scripts/{name}"))
    return sorted(files, key=lambda item: item[1])


def manifest_bytes(files: list[tuple[Path, str]]) -> bytes:
    lines = [
        "ERIKSSON PUBLICATION AUDIT — OWNER HAND-OFF",
        "CORPUS_FREEZE_DATE: 2026-07-31",
        "PUBLIC_RECORD_COUNT: 103",
        "PUBLIC_CURRENT_PDFS_AVAILABLE: 102",
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
    manifest_path = FINAL / "PUBLICATION-AUDIT-FINAL-MANIFEST.txt"
    zip_path = FINAL / "PUBLICATION-AUDIT-20260731.zip"
    sha_path = FINAL / "PUBLICATION-AUDIT-20260731-ZIP-SHA256.txt"
    manifest_path.write_bytes(manifest)
    with zipfile.ZipFile(zip_path, "w", compresslevel=9) as archive:
        for path, arcname in files:
            archive.writestr(info(arcname), path.read_bytes())
        archive.writestr(info(manifest_path.name), manifest)
    with zipfile.ZipFile(zip_path) as archive:
        if archive.read(manifest_path.name) != manifest_path.read_bytes():
            raise RuntimeError("internal and external final manifests differ")
        for path, arcname in files:
            if hashlib.sha256(archive.read(arcname)).hexdigest() != sha256(path):
                raise RuntimeError(f"final ZIP member mismatch: {arcname}")
    digest = sha256(zip_path)
    sha_path.write_text(f"{digest}  {zip_path.name}\n", encoding="ascii", newline="\n")
    print(f"PASS {zip_path.name} {digest} ({zip_path.stat().st_size} bytes)")
    print(f"PASS manifest internal=external SHA256 {hashlib.sha256(manifest).hexdigest()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
