#!/usr/bin/env python3
"""Build the vector-only page-6 repair for public paper 2601.0115v2.

The source PDF is treated as immutable.  Pages 1-5 and 7-9 are cloned without
content transformation.  Page 6 alone is wrapped in a uniform affine
transformation so that the complete Table 1 is inside the original Letter
MediaBox.  No rasterization is used.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path

from pypdf import PdfReader, PdfWriter, Transformation


PACKAGE_DIR = Path(__file__).resolve().parent
SOURCE_PDF = PACKAGE_DIR / "inputs/2601.0115v2-public-e845b2d99067.pdf"
EXPECTED_SOURCE_SHA256 = (
    "e845b2d9906714b04d525b82ed1c3c53d38238c3377ecb23417a69391a0e1382"
)

# Original full paint bounds on page 6 (MuPDF top-down coordinates):
# x = [71.239967, 540.214844], y = [72.000015, 869.844055] pt.
# In PDF bottom-up coordinates the lower painted edge is -77.844055 pt.
# A uniform 0.9 scale plus this translation centers the painted width and
# places the vertical painted bounds at approximately [36, 754.2] pt.
SCALE = 0.9
TRANSLATE_X = 31.0
TRANSLATE_Y = 106.1


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def build(output_dir: Path) -> Path:
    if not SOURCE_PDF.is_file():
        raise SystemExit(f"source PDF not found: {SOURCE_PDF}")
    source_hash = sha256(SOURCE_PDF)
    if source_hash != EXPECTED_SOURCE_SHA256:
        raise SystemExit(
            f"source SHA256 mismatch: expected {EXPECTED_SOURCE_SHA256}, got {source_hash}"
        )

    reader = PdfReader(str(SOURCE_PDF))
    if reader.is_encrypted or len(reader.pages) != 9:
        raise SystemExit("source must be an unencrypted 9-page PDF")
    if reader.pages[5].get("/Annots"):
        raise SystemExit("page 6 unexpectedly has annotations; transform would need review")

    writer = PdfWriter()
    writer.pdf_header = reader.pdf_header
    writer.clone_document_from_reader(reader)
    writer.pages[5].add_transformation(
        Transformation()
        .scale(sx=SCALE, sy=SCALE)
        .translate(tx=TRANSLATE_X, ty=TRANSLATE_Y),
        expand=False,
    )

    output_dir.mkdir(parents=True, exist_ok=True)
    for stale in output_dir.glob("2601.0115v3-P2-*.pdf"):
        stale.unlink()
    temporary = output_dir / "2601.0115v3-P2-building.pdf"
    with temporary.open("wb") as stream:
        writer.write(stream)

    final_hash = sha256(temporary)
    final = output_dir / f"2601.0115v3-P2-{final_hash[:12]}.pdf"
    if final.exists():
        final.unlink()
    temporary.replace(final)

    status = output_dir / "BUILD-STATUS.txt"
    status.write_text(
        "\n".join(
            [
                "STATUS: BUILT-NOT-AUDITED",
                f"SOURCE: {SOURCE_PDF}",
                f"SOURCE_SHA256: {source_hash}",
                "SOURCE_PAGES: 9",
                "MODIFIED_PAGE: 6",
                f"TRANSFORM: {SCALE} 0 0 {SCALE} {TRANSLATE_X} {TRANSLATE_Y} cm",
                f"OUTPUT: {final.name}",
                f"OUTPUT_SHA256: {final_hash}",
                "OUTPUT_PAGES: 9",
                "",
            ]
        ),
        encoding="utf-8",
    )
    print(final)
    print(final_hash)
    return final


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=PACKAGE_DIR / "artifacts",
        help="directory for the hash-named PDF and BUILD-STATUS.txt",
    )
    args = parser.parse_args()
    build(args.output_dir.resolve())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
