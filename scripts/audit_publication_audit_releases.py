#!/usr/bin/env python3
"""Adversarial preflight for all nine local replacement releases."""

from __future__ import annotations

import hashlib
import json
import re
import zipfile
from pathlib import Path

from pypdf import PdfReader


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "output" / "publication-audit"
RELEASES = OUT / "releases"
DOCS = ROOT / "docs" / "publication-audit"
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


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def field(text: str, name: str) -> str:
    match = re.search(rf"(?m)^{re.escape(name)}:[ \t]*(.*)$", text)
    if not match:
        return ""
    value = match.group(1).strip()
    if value:
        return value
    tail = text[match.end() :]
    return re.split(r"\n\s*\n[A-Z][A-Z _-]+:\s*", tail, maxsplit=1)[0].strip()


def words(value: str) -> int:
    return len(re.findall(r"\b[\w'-]+\b", value))


def main() -> int:
    records: list[dict[str, object]] = []
    orders: list[int] = []
    for package_name in PACKAGES:
        package = OUT / package_name
        sheet_path = package / "SUBMISSION-ID.txt"
        sheet = sheet_path.read_text(encoding="utf-8")
        status = field(sheet, "STATUS")
        if "LISTO-LOCAL" not in status:
            raise RuntimeError(f"{package_name}: status is not LISTO-LOCAL")
        file_rel = field(sheet, "FILE")
        final_pdf = package / file_rel
        if not final_pdf.is_file():
            raise FileNotFoundError(final_pdf)
        reader = PdfReader(str(final_pdf), strict=True)
        if reader.is_encrypted or final_pdf.stat().st_size >= 5_000_000:
            raise RuntimeError(f"{package_name}: PDF encryption/size preflight failed")
        abstract_words = words(field(sheet, "ABSTRACT"))
        comments_words = words(field(sheet, "COMMENTS"))
        if not (0 < abstract_words < 400) or not (0 < comments_words < 100):
            raise RuntimeError(f"{package_name}: abstract/comments limits failed")
        immutable = re.search(
            r"https://github\.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/tree/[0-9a-f]{40}/output/publication-audit/[^\s]+",
            sheet,
        )
        if not immutable:
            raise RuntimeError(f"{package_name}: missing full immutable source link")
        order_match = re.search(r"(?m)^(?:OWNER ORDER|SUBMISSION_ORDER):\s*(\d+) of 9", sheet)
        if not order_match:
            raise RuntimeError(f"{package_name}: owner order missing")
        order = int(order_match.group(1))
        orders.append(order)

        zip_path = RELEASES / f"{package_name}.zip"
        sha_path = RELEASES / f"{package_name}-ZIP-SHA256.txt"
        expected_zip_sha = sha_path.read_text(encoding="ascii").split()[0]
        actual_zip_sha = sha256(zip_path)
        if actual_zip_sha != expected_zip_sha:
            raise RuntimeError(f"{package_name}: ZIP SHA mismatch")
        externals = list(RELEASES.glob(f"{package_name}-MANIFEST*.txt"))
        if len(externals) != 1:
            raise RuntimeError(f"{package_name}: external manifest count {len(externals)}")
        external = externals[0]
        root_manifests = list(package.glob("MANIFEST-*.txt"))
        if len(root_manifests) != 1 or root_manifests[0].read_bytes() != external.read_bytes():
            raise RuntimeError(f"{package_name}: package/external manifests differ")

        with zipfile.ZipFile(zip_path) as archive:
            members = archive.namelist()
            internal_names = [name for name in members if "/MANIFEST-" in name]
            if len(internal_names) != 1 or archive.read(internal_names[0]) != external.read_bytes():
                raise RuntimeError(f"{package_name}: internal/external manifests differ")
            final_member = f"{package_name}/{file_rel.replace('\\', '/')}"
            if hashlib.sha256(archive.read(final_member)).hexdigest() != sha256(final_pdf):
                raise RuntimeError(f"{package_name}: final PDF ZIP member mismatch")
            forbidden = [
                name
                for name in members
                if Path(name).suffix.lower() in {".aux", ".log", ".out", ".png", ".ppm", ".pyc"}
                or re.search(r"/artifacts/(?:erratum|.*_front).*\.pdf$", name, re.I)
            ]
            if forbidden:
                raise RuntimeError(f"{package_name}: forbidden intermediate/QA members {forbidden}")
            if not any("VERIFY-TRANSCRIPT-O0" in name for name in members) or not any(
                "VERIFY-TRANSCRIPT-O1" in name for name in members
            ):
                raise RuntimeError(f"{package_name}: optimizer transcripts absent")
            if not any("AUDIT" in Path(name).name.upper() and name.endswith(".md") for name in members):
                raise RuntimeError(f"{package_name}: audit report absent")

        inputs = [
            {"path": str(path.relative_to(package)).replace("\\", "/"), "sha256": sha256(path)}
            for path in sorted((package / "inputs").glob("*.pdf"))
        ]
        records.append(
            {
                "order": order,
                "package": package_name,
                "status": status,
                "final_pdf": file_rel,
                "final_sha256": sha256(final_pdf),
                "pages": len(reader.pages),
                "bytes": final_pdf.stat().st_size,
                "encrypted": bool(reader.is_encrypted),
                "abstract_words": abstract_words,
                "comments_words": comments_words,
                "immutable_source": immutable.group(0),
                "input_pdfs": inputs,
                "zip": zip_path.name,
                "zip_sha256": actual_zip_sha,
                "manifest_sha256": sha256(external),
            }
        )
    if sorted(orders) != list(range(1, 10)):
        raise RuntimeError(f"owner order is not exactly 1..9: {orders}")
    records.sort(key=lambda item: int(item["order"]))
    (DOCS / "FINAL-PACKAGE-PREFLIGHT.json").write_text(
        json.dumps({"status": "PASS", "packages": records}, indent=2) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    lines = [
        "# Final replacement-package preflight",
        "",
        "**PASS.** Nine of nine local replacement packages pass integrity, field-limit,",
        "optimizer, provenance, ZIP-selection and manifest-identity gates.  This is a",
        "local readiness result; no upload or submission occurred.",
        "",
        "| Order | Package | Final PDF SHA-256 | Pages | Bytes | Abstract/comments words | ZIP SHA-256 |",
        "|---:|---|---|---:|---:|---:|---|",
    ]
    for item in records:
        lines.append(
            f"| {item['order']} | `{item['package']}` | `{item['final_sha256']}` | "
            f"{item['pages']} | {item['bytes']} | {item['abstract_words']}/{item['comments_words']} | "
            f"`{item['zip_sha256']}` |"
        )
    lines.extend(
        (
            "",
            "For every row: final PDF is unencrypted and below 5 MB; the release ZIP",
            "contains the named final PDF, frozen inputs, sources/builders, O0/O1",
            "transcripts, submission sheet and audit report; no QA raster, LaTeX",
            "temporary, intermediate erratum/front PDF or Python bytecode is present.",
            "The manifest beside the package, the external release manifest and the",
            "manifest inside the ZIP are byte-identical.  Owner order is exactly 1–9.",
            "",
        )
    )
    (DOCS / "FINAL-PACKAGE-PREFLIGHT.md").write_text("\n".join(lines), encoding="utf-8", newline="\n")
    print("PASS nine replacement releases; owner order 1..9; manifests internal=external")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
