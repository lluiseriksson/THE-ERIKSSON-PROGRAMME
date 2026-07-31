#!/usr/bin/env python3
"""Mechanical and pixel verification for the 2601.0115v3 P2 repair."""

from __future__ import annotations

import hashlib
import ast
import re
import subprocess
import sys
import tempfile
from pathlib import Path

import fitz
from pypdf import PdfReader


PACKAGE_DIR = Path(__file__).resolve().parent
REPO_ROOT = PACKAGE_DIR.parents[2]
ARTIFACT_DIR = PACKAGE_DIR / "artifacts"
SOURCE = PACKAGE_DIR / "inputs/2601.0115v2-public-e845b2d99067.pdf"
FROZEN_PUBLIC_SOURCE = REPO_ROOT / "tmp/publication-audit/public-pdfs/2601.0115v2.pdf"
SOURCE_SHA256 = "e845b2d9906714b04d525b82ed1c3c53d38238c3377ecb23417a69391a0e1382"
EXPECTED_PAGES = 9
PAGE6_INDEX = 5


def file_hash(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def traced_chars(page: fitz.Page) -> list[tuple[int, tuple[float, float, float, float]]]:
    result: list[tuple[int, tuple[float, float, float, float]]] = []
    for span in page.get_texttrace():
        for char in span["chars"]:
            result.append((int(char[0]), tuple(float(v) for v in char[3])))
    return result


def outside_count(chars: list[tuple[int, tuple[float, float, float, float]]], width: float, height: float) -> int:
    return sum(
        1
        for _, (x0, y0, x1, y1) in chars
        if x0 < 0 or y0 < 0 or x1 > width or y1 > height
    )


def page_pixel_hash(page: fitz.Page) -> str:
    pixmap = page.get_pixmap(matrix=fitz.Matrix(2.0, 2.0), alpha=False)
    return hashlib.sha256(pixmap.samples).hexdigest()


def main() -> int:
    lines: list[str] = []
    failures: list[str] = []

    def check(condition: bool, label: str, detail: str = "") -> None:
        status = "PASS" if condition else "FAIL"
        suffix = f" - {detail}" if detail else ""
        lines.append(f"{status}: {label}{suffix}")
        if not condition:
            failures.append(label)

    lines.append("2601.0115v3 P2 VECTOR-REPAIR VERIFICATION")
    lines.append(f"PYTHON_OPTIMIZE: {sys.flags.optimize}")
    lines.append(f"PYTHON: {sys.version.split()[0]}")

    candidates = sorted(ARTIFACT_DIR.glob("2601.0115v3-P2-*.pdf"))
    check(len(candidates) == 1, "exactly one final artifact", str([p.name for p in candidates]))
    if len(candidates) != 1:
        transcript = ARTIFACT_DIR / f"VERIFY-TRANSCRIPT-O{sys.flags.optimize}.txt"
        transcript.write_text("\n".join(lines + ["STATUS: FAIL", ""]), encoding="utf-8")
        print(transcript.read_text(encoding="utf-8"), end="")
        return 1
    final = candidates[0]
    final_hash = file_hash(final)
    check(file_hash(SOURCE) == SOURCE_SHA256, "frozen source SHA256", file_hash(SOURCE))
    check(
        FROZEN_PUBLIC_SOURCE.is_file() and file_hash(FROZEN_PUBLIC_SOURCE) == file_hash(SOURCE),
        "packaged input is byte-identical to frozen public PDF",
    )
    name_match = re.fullmatch(r"2601\.0115v3-P2-([0-9a-f]{12})\.pdf", final.name)
    check(name_match is not None, "hash-named output format", final.name)
    check(name_match is not None and name_match.group(1) == final_hash[:12], "filename hash prefix", final_hash)

    source_reader = PdfReader(str(SOURCE))
    final_reader = PdfReader(str(final))
    check(not source_reader.is_encrypted and not final_reader.is_encrypted, "source and output unencrypted")
    check(len(source_reader.pages) == EXPECTED_PAGES, "source page count", str(len(source_reader.pages)))
    check(len(final_reader.pages) == EXPECTED_PAGES, "output page count", str(len(final_reader.pages)))
    boxes_equal = all(
        list(map(float, source_reader.pages[i].mediabox))
        == list(map(float, final_reader.pages[i].mediabox))
        == [0.0, 0.0, 612.0, 792.0]
        for i in range(EXPECTED_PAGES)
    )
    check(boxes_equal, "all Letter MediaBoxes preserved")
    check(not final_reader.pages[PAGE6_INDEX].get("/Annots"), "page 6 remains annotation-free")

    source_doc = fitz.open(SOURCE)
    final_doc = fitz.open(final)
    source_chars = traced_chars(source_doc[PAGE6_INDEX])
    final_chars = traced_chars(final_doc[PAGE6_INDEX])
    source_outside = outside_count(source_chars, 612.0, 792.0)
    final_outside = outside_count(final_chars, 612.0, 792.0)
    check(source_outside == 152, "source page 6 has diagnosed out-of-MediaBox characters", str(source_outside))
    check(final_outside == 0, "output page 6 has no out-of-MediaBox characters", str(final_outside))
    check(
        [codepoint for codepoint, _ in source_chars] == [codepoint for codepoint, _ in final_chars],
        "page 6 character sequence preserved",
        f"{len(source_chars)} traced characters",
    )

    paint_boxes = [box for _, box in final_doc[PAGE6_INDEX].get_bboxlog()]
    min_x = min(box[0] for box in paint_boxes)
    min_y = min(box[1] for box in paint_boxes)
    max_x = max(box[2] for box in paint_boxes)
    max_y = max(box[3] for box in paint_boxes)
    check(
        min_x >= 30 and min_y >= 30 and max_x <= 582 and max_y <= 762,
        "page 6 full paint bounds have >=30 pt safety margin",
        f"x=[{min_x:.3f},{max_x:.3f}], y=[{min_y:.3f},{max_y:.3f}]",
    )
    full_text = final_doc[PAGE6_INDEX].get_text("text", clip=fitz.Rect(-1000, -1000, 2000, 2000))
    check("Table1:" in "".join(full_text.split()), "Table 1 label extractable")
    check("Isum" in full_text, "Table 1 final row extractable")

    unchanged = [i for i in range(EXPECTED_PAGES) if i != PAGE6_INDEX]
    source_pixels = [page_pixel_hash(source_doc[i]) for i in range(EXPECTED_PAGES)]
    final_pixels = [page_pixel_hash(final_doc[i]) for i in range(EXPECTED_PAGES)]
    mismatches = [i + 1 for i in unchanged if source_pixels[i] != final_pixels[i]]
    check(not mismatches, "pages 1-5 and 7-9 pixel-identical at 144 dpi", str(mismatches))
    check(source_pixels[PAGE6_INDEX] != final_pixels[PAGE6_INDEX], "page 6 rendering changed")

    with tempfile.TemporaryDirectory(prefix="verify-2601-0115-") as temp:
        rebuilt_dir = Path(temp)
        proc = subprocess.run(
            [sys.executable, str(PACKAGE_DIR / "build_2601_0115_v3.py"), "--output-dir", str(rebuilt_dir)],
            capture_output=True,
            text=True,
            check=False,
        )
        rebuilt = sorted(rebuilt_dir.glob("2601.0115v3-P2-*.pdf"))
        check(proc.returncode == 0 and len(rebuilt) == 1, "clean rebuild succeeds", proc.stdout.strip())
        check(len(rebuilt) == 1 and file_hash(rebuilt[0]) == final_hash, "clean rebuild is byte-identical", final_hash)

    verifier_tree = ast.parse(Path(__file__).read_text(encoding="utf-8"))
    check(
        not any(isinstance(node, ast.Assert) for node in ast.walk(verifier_tree)),
        "verifier contains no assertion nodes",
    )
    status = "PASS" if not failures else "FAIL"
    lines.append(f"OUTPUT: {final.name}")
    lines.append(f"OUTPUT_SHA256: {final_hash}")
    lines.append(f"STATUS: {status}")
    transcript = ARTIFACT_DIR / f"VERIFY-TRANSCRIPT-O{sys.flags.optimize}.txt"
    transcript.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))
    return 0 if not failures else 1


if __name__ == "__main__":
    raise SystemExit(main())
