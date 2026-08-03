#!/usr/bin/env python3
"""Build deterministic, self-verifying replacement-package ZIP files.

The external package manifest, the manifest next to the working package, and
the package manifest member inside the ZIP are byte-identical.  The manifest lists
the payload but not itself, avoiding a recursive hash definition.  ZIP-SHA256
is necessarily external because it hashes the completed ZIP.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import sys
import zipfile
from datetime import date
from pathlib import Path

from pypdf import PdfReader


ROOT = Path(__file__).resolve().parents[1]
PACKAGES = ROOT / "output" / "publication-audit"
RELEASES = PACKAGES / "releases"
DEFAULT_AUDIT_DATE = "2026-07-31"


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def parse_submission(path: Path) -> dict[str, str]:
    text = path.read_text(encoding="utf-8")
    fields: dict[str, str] = {}
    for key in ("STATUS", "AUDIT DATE", "PUBLICATION ACTION", "PUBLICATION", "CATEGORY", "FILE"):
        match = re.search(rf"(?m)^{re.escape(key)}:\s*(.+)$", text)
        if match:
            fields[key] = match.group(1).strip()
    if "PUBLICATION ACTION" not in fields:
        match = re.search(r"(?m)^ACTION:\s*(.+)$", text)
        if match:
            fields["PUBLICATION ACTION"] = match.group(1).strip()
    if "PUBLICATION" not in fields:
        match = re.search(r"(?m)^PUBLIC RECORD:\s*https?://[^\s]+/(\d{4}\.\d{4})\s*$", text)
        if match:
            fields["PUBLICATION"] = f"ai.viXra.org:{match.group(1)}"
    if "FILE" not in fields:
        raise ValueError(f"missing FILE field in {path}")
    return fields


def payload_files(package: Path, final_rel: str) -> list[Path]:
    final = package / Path(final_rel)
    if not final.is_file():
        raise FileNotFoundError(f"submission PDF does not exist: {final}")

    keep: set[Path] = {final}
    for path in package.iterdir():
        if not path.is_file():
            continue
        if path.name.upper().startswith("MANIFEST") or path.name.endswith("-SHA256.txt"):
            continue
        if path.suffix.lower() in {".py", ".md", ".txt", ".json"}:
            keep.add(path)

    for subdir in ("src", "inputs"):
        root = package / subdir
        if root.is_dir():
            keep.update(path for path in root.rglob("*") if path.is_file())

    artifacts = package / "artifacts"
    if artifacts.is_dir():
        for path in artifacts.iterdir():
            if not path.is_file() or path == final:
                continue
            name = path.name.upper()
            if (
                path.suffix.lower() in {".txt", ".md", ".json"}
                and ("TRANSCRIPT" in name or "STATUS" in name or "RESULT" in name or "AUDIT" in name)
            ):
                keep.add(path)

    forbidden = {".aux", ".log", ".out", ".png", ".ppm", ".pyc"}
    selected = sorted(
        (p for p in keep if p.suffix.lower() not in forbidden and "__pycache__" not in p.parts),
        key=lambda p: p.relative_to(package).as_posix(),
    )
    return selected


def manifest_bytes(package: Path, fields: dict[str, str], files: list[Path]) -> bytes:
    final = package / fields["FILE"]
    reader = PdfReader(str(final))
    encrypted = bool(reader.is_encrypted)
    lines = [
        "ERIKSSON PUBLICATION-AUDIT REPLACEMENT PACKAGE",
        f"AUDIT_DATE: {fields.get('AUDIT DATE', DEFAULT_AUDIT_DATE)}",
        f"PACKAGE: {package.name}",
        f"STATUS: {fields.get('STATUS', 'NOT RECORDED')}",
        f"ACTION: {fields.get('PUBLICATION ACTION', 'NOT RECORDED')}",
        f"PUBLICATION: {fields.get('PUBLICATION', 'NOT RECORDED')}",
        f"CATEGORY: {fields.get('CATEGORY', 'NOT RECORDED')}",
        f"FINAL_PDF: {fields['FILE']}",
        f"FINAL_PDF_SHA256: {sha256(final)}",
        f"FINAL_PDF_BYTES: {final.stat().st_size}",
        f"FINAL_PDF_PAGES: {len(reader.pages)}",
        f"FINAL_PDF_ENCRYPTED: {'yes' if encrypted else 'no'}",
        "MANIFEST_SCOPE: payload files; the manifest excludes itself by definition",
        "",
        "SHA256  BYTES  PATH",
    ]
    for path in files:
        rel = path.relative_to(package).as_posix()
        lines.append(f"{sha256(path)}  {path.stat().st_size}  {rel}")
    lines.extend(("", f"PAYLOAD_FILE_COUNT: {len(files)}", ""))
    return "\n".join(lines).encode("utf-8")


def manifest_name(package: Path) -> str:
    if package.name == "2601.0115-v3":
        return "MANIFEST-2601.0115-V3.txt"
    if package.name == "2602.0033-r30":
        return "MANIFEST-R30.txt"
    return f"MANIFEST-{package.name}.txt"


def write_zip(
    package: Path,
    files: list[Path],
    manifest: bytes,
    manifest_basename: str,
    zip_path: Path,
    zip_time: tuple[int, int, int, int, int, int],
) -> None:
    def info(name: str) -> zipfile.ZipInfo:
        item = zipfile.ZipInfo(name, zip_time)
        item.compress_type = zipfile.ZIP_DEFLATED
        item.create_system = 3
        item.external_attr = 0o100644 << 16
        return item

    prefix = package.name
    with zipfile.ZipFile(zip_path, "w", compresslevel=9) as archive:
        for path in files:
            rel = path.relative_to(package).as_posix()
            archive.writestr(info(f"{prefix}/{rel}"), path.read_bytes())
        archive.writestr(info(f"{prefix}/{manifest_basename}"), manifest)


def verify_release(
    package: Path, files: list[Path], manifest: bytes, manifest_basename: str, zip_path: Path
) -> None:
    with zipfile.ZipFile(zip_path) as archive:
        internal = archive.read(f"{package.name}/{manifest_basename}")
        if internal != manifest:
            raise RuntimeError("internal and external manifests differ")
        expected = {f"{package.name}/{p.relative_to(package).as_posix()}" for p in files}
        expected.add(f"{package.name}/{manifest_basename}")
        if set(archive.namelist()) != expected:
            raise RuntimeError("ZIP member set differs from selected payload")
        for path in files:
            member = f"{package.name}/{path.relative_to(package).as_posix()}"
            if hashlib.sha256(archive.read(member)).hexdigest() != sha256(path):
                raise RuntimeError(f"ZIP member hash mismatch: {member}")


def build(name: str) -> None:
    package = PACKAGES / name
    if not package.is_dir():
        raise FileNotFoundError(package)
    sheet = package / "SUBMISSION-ID.txt"
    fields = parse_submission(sheet)
    files = payload_files(package, fields["FILE"])
    manifest = manifest_bytes(package, fields, files)

    RELEASES.mkdir(parents=True, exist_ok=True)
    manifest_basename = manifest_name(package)
    package_manifest = package / manifest_basename
    external_manifest = RELEASES / f"{name}-{manifest_basename}"
    zip_path = RELEASES / f"{name}.zip"
    sha_path = RELEASES / f"{name}-ZIP-SHA256.txt"
    package_manifest.write_bytes(manifest)
    external_manifest.write_bytes(manifest)
    audit_date = date.fromisoformat(fields.get("AUDIT DATE", DEFAULT_AUDIT_DATE))
    zip_time = (audit_date.year, audit_date.month, audit_date.day, 0, 0, 0)
    write_zip(package, files, manifest, manifest_basename, zip_path, zip_time)
    verify_release(package, files, manifest, manifest_basename, zip_path)
    digest = sha256(zip_path)
    sha_path.write_text(f"{digest}  {zip_path.name}\n", encoding="ascii", newline="\n")
    if package_manifest.read_bytes() != external_manifest.read_bytes():
        raise RuntimeError("package and external manifests differ")
    print(f"PASS {name}: {zip_path.name} {digest} ({zip_path.stat().st_size} bytes)")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("packages", nargs="+", help="package directory names")
    args = parser.parse_args()
    for name in args.packages:
        build(name)
    return 0


if __name__ == "__main__":
    sys.exit(main())
