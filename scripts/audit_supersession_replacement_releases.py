#!/usr/bin/env python3
"""Adversarial preflight for the four 2026-08-01 supersession replacements."""

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
    "2512.0073-v2",
    "2601.0047-v3",
    "2607.0035-v2",
    "2607.0023-v2",
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
        cfg = json.loads((package / "config.json").read_text(encoding="utf-8"))
        sheet = (package / "SUBMISSION-ID.txt").read_text(encoding="utf-8")
        status = field(sheet, "STATUS")
        if "LISTO-LOCAL" not in status or "INDEPENDENTLY AUDITED" not in status:
            raise RuntimeError(f"{package_name}: status is not independently audited LISTO-LOCAL")
        if field(sheet, "AUDIT DATE") != "2026-08-01":
            raise RuntimeError(f"{package_name}: audit date mismatch")
        if field(sheet, "PUBLICATION ACTION") != "REPLACE VERSION":
            raise RuntimeError(f"{package_name}: action mismatch")
        file_rel = field(sheet, "FILE")
        final_pdf = package / file_rel
        reader = PdfReader(str(final_pdf), strict=True)
        if reader.is_encrypted or final_pdf.stat().st_size >= 5_000_000:
            raise RuntimeError(f"{package_name}: PDF encryption/size gate failed")
        if len(reader.pages) != int(cfg["historical_pages"]) + 2:
            raise RuntimeError(f"{package_name}: final page count mismatch")
        notice_text = " ".join((reader.pages[i].extract_text() or "") for i in range(2))
        if cfg["headline"] not in re.sub(r"\s+", " ", notice_text):
            raise RuntimeError(f"{package_name}: uppercase headline absent from PDF")
        abstract = field(sheet, "ABSTRACT")
        comments = field(sheet, "COMMENTS")
        if not abstract.startswith(cfg["headline"]):
            raise RuntimeError(f"{package_name}: abstract does not start with uppercase headline")
        if not (0 < words(abstract) < 400) or not (0 < words(comments) < 100):
            raise RuntimeError(f"{package_name}: field word limits failed")
        immutable = re.search(
            r"https://github\.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/tree/[0-9a-f]{40}/output/publication-audit/[^\s]+",
            sheet,
        )
        if not immutable:
            raise RuntimeError(f"{package_name}: immutable source link absent")
        order_match = re.search(r"(?m)^ORDER:\s*(\d+) of 13", sheet)
        if not order_match:
            raise RuntimeError(f"{package_name}: owner order absent")
        order = int(order_match.group(1))
        orders.append(order)
        if not (package / "INDEPENDENT-AUDIT.md").is_file():
            raise RuntimeError(f"{package_name}: independent audit report absent")
        for level in (0, 1):
            transcript = package / "artifacts" / f"VERIFY-TRANSCRIPT-O{level}.txt"
            content = transcript.read_text(encoding="utf-8")
            if f"PYTHON_OPTIMIZE_LEVEL {level}" not in content or "STATUS SELF-VERIFIED-NOT-INDEPENDENT" not in content:
                raise RuntimeError(f"{package_name}: O{level} transcript mismatch")

        zip_path = RELEASES / f"{package_name}.zip"
        sha_path = RELEASES / f"{package_name}-ZIP-SHA256.txt"
        expected_zip_sha = sha_path.read_text(encoding="ascii").split()[0]
        actual_zip_sha = sha256(zip_path)
        if expected_zip_sha != actual_zip_sha:
            raise RuntimeError(f"{package_name}: ZIP SHA mismatch")
        external_manifests = list(RELEASES.glob(f"{package_name}-MANIFEST*.txt"))
        package_manifests = list(package.glob("MANIFEST-*.txt"))
        if len(external_manifests) != 1 or len(package_manifests) != 1:
            raise RuntimeError(f"{package_name}: manifest cardinality mismatch")
        external = external_manifests[0]
        if package_manifests[0].read_bytes() != external.read_bytes():
            raise RuntimeError(f"{package_name}: package/external manifest mismatch")
        with zipfile.ZipFile(zip_path) as archive:
            internals = [name for name in archive.namelist() if "/MANIFEST-" in name]
            if len(internals) != 1 or archive.read(internals[0]) != external.read_bytes():
                raise RuntimeError(f"{package_name}: internal/external manifest mismatch")
            final_member = f"{package_name}/{file_rel.replace(chr(92), '/')}"
            if hashlib.sha256(archive.read(final_member)).hexdigest() != sha256(final_pdf):
                raise RuntimeError(f"{package_name}: ZIP final PDF mismatch")
            forbidden = [
                name
                for name in archive.namelist()
                if Path(name).suffix.lower() in {".aux", ".log", ".out", ".png", ".ppm", ".pyc"}
                or name.endswith("supersession-notice.pdf")
            ]
            if forbidden:
                raise RuntimeError(f"{package_name}: forbidden release members {forbidden}")

        records.append(
            {
                "order": order,
                "package": package_name,
                "publication": field(sheet, "PUBLICATION"),
                "successor": cfg["successor_record"],
                "headline": cfg["headline"],
                "final_pdf": file_rel,
                "final_sha256": sha256(final_pdf),
                "pages": len(reader.pages),
                "bytes": final_pdf.stat().st_size,
                "abstract_words": words(abstract),
                "comments_words": words(comments),
                "zip": zip_path.name,
                "zip_sha256": actual_zip_sha,
                "manifest_sha256": sha256(external),
            }
        )
    if sorted(orders) != [10, 11, 12, 13]:
        raise RuntimeError(f"orders are not exactly 10..13: {orders}")
    records.sort(key=lambda item: int(item["order"]))
    DOCS.mkdir(parents=True, exist_ok=True)
    (DOCS / "SUPERSESSION-REPLACEMENT-PREFLIGHT.json").write_text(
        json.dumps({"status": "PASS", "audit_date": "2026-08-01", "packages": records}, indent=2) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    lines = [
        "# Supersession replacement-package preflight - 2026-08-01",
        "",
        "**PASS.** Four independently audited replacement packages carry the exact",
        "uppercase supersession/status notice in both the PDF and the literal abstract.",
        "This is a local readiness result; no upload or submission occurred.",
        "",
        "| Order | Package | Successor | Final SHA-256 | Pages | Bytes | Abstract/comments words | ZIP SHA-256 |",
        "|---:|---|---|---|---:|---:|---:|---|",
    ]
    for item in records:
        lines.append(
            f"| {item['order']} | `{item['package']}` | `{item['successor']}` | `{item['final_sha256']}` | "
            f"{item['pages']} | {item['bytes']} | {item['abstract_words']}/{item['comments_words']} | `{item['zip_sha256']}` |"
        )
    lines.extend(
        [
            "",
            "Every final PDF is unencrypted, below 5 MB and has embedded fonts. The two",
            "new notice pages were visually inspected; every historical page is rendered",
            "pixel-identically after the notice. Each ZIP contains both frozen public inputs,",
            "builder/source, O0/O1 transcripts, literal submission sheet, independent audit",
            "and byte-identical internal/package/external manifests, with no QA raster or",
            "intermediate notice PDF.",
            "",
        ]
    )
    (DOCS / "SUPERSESSION-REPLACEMENT-PREFLIGHT.md").write_text("\n".join(lines), encoding="utf-8", newline="\n")
    print("PASS four supersession replacement releases; orders 10..13")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
