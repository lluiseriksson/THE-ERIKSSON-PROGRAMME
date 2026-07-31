#!/usr/bin/env python3
"""Extract and render every available public-census PDF for visual audit."""

from __future__ import annotations

import argparse
import json
import math
import shutil
import subprocess
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont


POPPLER = Path(
    r"C:\Users\lluis\.cache\codex-runtimes\codex-primary-runtime"
    r"\dependencies\native\poppler\Library\bin"
)
PDFTOPPM = POPPLER / "pdftoppm.exe"
PDFTOTEXT = Path(r"C:\Users\lluis\AppData\Local\Programs\MiKTeX\miktex\bin\x64\pdftotext.exe")


def command(argv: list[str]) -> None:
    completed = subprocess.run(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if completed.returncode:
        raise RuntimeError(
            f"command failed ({completed.returncode}): {argv!r}\n{completed.stdout}\n{completed.stderr}"
        )


def make_sheet(images: list[Path], destination: Path, label: str) -> None:
    opened = [Image.open(path).convert("RGB") for path in images]
    try:
        width = max(image.width for image in opened)
        height = max(image.height for image in opened)
        header = 44
        gutter = 12
        canvas = Image.new(
            "RGB", (2 * width + gutter, 2 * (height + header) + gutter), "white"
        )
        draw = ImageDraw.Draw(canvas)
        font = ImageFont.load_default(size=20)
        for index, (path, image) in enumerate(zip(images, opened)):
            row, col = divmod(index, 2)
            x = col * (width + gutter)
            y = row * (height + header + gutter)
            draw.text((x + 8, y + 8), f"{label} / {path.stem}", fill="black", font=font)
            canvas.paste(image, (x, y + header))
        destination.parent.mkdir(parents=True, exist_ok=True)
        canvas.save(destination, "PNG", optimize=True)
    finally:
        for image in opened:
            image.close()


def render_one(record: dict, output_root: Path, dpi: int) -> dict:
    pdf = Path(record["pdf_local_path"])
    key = f"{record['id']}v{record['current_version']}"
    text_dir = output_root / "text"
    page_dir = output_root / "rendered" / key
    sheet_dir = output_root / "contact-sheets"
    text_dir.mkdir(parents=True, exist_ok=True)
    page_dir.mkdir(parents=True, exist_ok=True)
    expected_pages = int(record["pdfinfo"]["pages"])

    text_path = text_dir / f"{key}.txt"
    command([str(PDFTOTEXT), "-layout", str(pdf), str(text_path)])

    for stale in page_dir.glob("page-*.png"):
        stale.unlink()
    command([str(PDFTOPPM), "-r", str(dpi), "-png", str(pdf), str(page_dir / "page")])
    pages = sorted(page_dir.glob("page-*.png"))
    if len(pages) != expected_pages:
        raise RuntimeError(f"{key}: rendered {len(pages)} pages, expected {expected_pages}")

    for stale in sheet_dir.glob(f"{key}-sheet-*.png"):
        stale.unlink()
    sheets = []
    for offset in range(0, len(pages), 4):
        chunk = pages[offset : offset + 4]
        first = offset + 1
        last = offset + len(chunk)
        sheet = sheet_dir / f"{key}-sheet-{offset // 4 + 1:03d}-p{first:03d}-{last:03d}.png"
        make_sheet(chunk, sheet, key)
        sheets.append(str(sheet.resolve()))

    return {
        "id": record["id"],
        "version": record["current_version"],
        "pdf": str(pdf.resolve()),
        "pages": expected_pages,
        "text": str(text_path.resolve()),
        "render_directory": str(page_dir.resolve()),
        "contact_sheets": sheets,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--census", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--dpi", type=int, default=110)
    parser.add_argument("--workers", type=int, default=4)
    args = parser.parse_args()

    payload = json.loads(args.census.read_text(encoding="utf-8"))
    records = [record for record in payload["records"] if record.get("pdf_local_path")]
    args.output_root.mkdir(parents=True, exist_ok=True)
    results = []
    errors = []
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(render_one, record, args.output_root, args.dpi): record for record in records}
        for future in as_completed(futures):
            record = futures[future]
            try:
                results.append(future.result())
            except Exception as exc:  # retained in manifest; any error is fatal below
                errors.append({"id": record["id"], "error": str(exc)})

    results.sort(key=lambda item: item["id"])
    manifest = {
        "census": str(args.census.resolve()),
        "dpi": args.dpi,
        "rendered_pdfs": len(results),
        "rendered_pages": sum(item["pages"] for item in results),
        "contact_sheets": sum(len(item["contact_sheets"]) for item in results),
        "errors": errors,
        "records": results,
    }
    manifest_path = args.output_root / "render-manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8", newline="\n")
    print(json.dumps({key: manifest[key] for key in ("rendered_pdfs", "rendered_pages", "contact_sheets", "errors")}, indent=2))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
