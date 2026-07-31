#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

from PIL import Image, ImageChops
from pypdf import PdfReader


ROOT = Path(__file__).resolve().parent
ART = ROOT / "artifacts"


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def tool(name: str) -> str:
    fallback = Path(r"C:\Users\lluis\.cache\codex-runtimes\codex-primary-runtime\dependencies\native\poppler\Library\bin") / f"{name}.exe"
    if fallback.is_file():
        return str(fallback)
    found = shutil.which(name)
    if found:
        return found
    raise FileNotFoundError(name)


def main() -> int:
    level = sys.flags.optimize
    cfg = json.loads((ROOT / "config.json").read_text(encoding="utf-8"))
    result = json.loads((ART / "build-result.json").read_text(encoding="utf-8"))
    final = ART / cfg["final_filename"]
    historical = ROOT / "inputs" / cfg["historical_pdf"]
    successor = ROOT / "inputs" / cfg["successor_pdf"]
    sheet = (ROOT / "SUBMISSION-ID.txt").read_text(encoding="utf-8")
    lines = [f"PYTHON_OPTIMIZE_LEVEL {level}"]

    def check(value: bool, label: str) -> None:
        if not value:
            raise RuntimeError(label)
        lines.append(f"PASS {label}")

    check(final.is_file(), "final exists")
    check(sha256(final) == result["final_sha256"], "final SHA")
    check(sha256(historical) == cfg["historical_sha256"], "historical SHA")
    check(sha256(successor) == cfg["successor_sha256"], "successor SHA")
    reader = PdfReader(str(final), strict=True)
    old_reader = PdfReader(str(historical), strict=True)
    check(not reader.is_encrypted, "final unencrypted")
    check(len(reader.pages) == cfg["historical_pages"] + 2, "final page count")
    check(final.stat().st_size < 5_000_000, "final below 5 MB")
    first_text = " ".join((reader.pages[i].extract_text() or "") for i in range(2))
    check(cfg["headline"] in re.sub(r"\s+", " ", first_text), "uppercase supersession headline in PDF")
    abstract_match = re.search(r"(?ms)^ABSTRACT:\s*(.+?)\n\s*COMMENTS:", sheet)
    check(abstract_match is not None, "submission abstract parsed")
    check(abstract_match.group(1).lstrip().startswith(cfg["headline"]), "uppercase supersession headline starts abstract")
    check(cfg["successor_record"] in sheet, "successor ID in submission sheet")
    source_text = Path(__file__).read_text(encoding="utf-8")
    check(not re.search(r"(?m)^\s*as" + r"sert\b", source_text), "no optimizer-sensitive check statements")

    qa = ART / f"qa-o{level}"
    final_dir = qa / "final"
    input_dir = qa / "historical"
    for directory in (final_dir, input_dir):
        directory.mkdir(parents=True, exist_ok=True)
        for stale in directory.glob("*.png"):
            stale.unlink()
    for pdf, directory in ((final, final_dir), (historical, input_dir)):
        run = subprocess.run([tool("pdftoppm"), "-r", "120", "-png", str(pdf), str(directory / "page")], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        check(run.returncode == 0, f"render {pdf.name}")
    final_pages = sorted(final_dir.glob("*.png"))
    old_pages = sorted(input_dir.glob("*.png"))
    check(len(final_pages) == len(old_pages) + 2, "rendered page counts")
    for index, old in enumerate(old_pages):
        with Image.open(final_pages[index + 2]).convert("RGB") as a, Image.open(old).convert("RGB") as b:
            check(a.size == b.size and ImageChops.difference(a, b).getbbox() is None, f"historical page {index + 1} pixel-preserved")
    fonts = subprocess.run([tool("pdffonts"), str(final)], text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    check(fonts.returncode == 0, "font inventory readable")
    font_rows = [line for line in fonts.stdout.splitlines()[2:] if line.strip()]
    font_flags = [re.search(r"\s+(yes|no)\s+(yes|no)\s+(yes|no)\s+\d+\s+\d+\s*$", line) for line in font_rows]
    check(bool(font_flags) and all(match is not None and match.group(1) == "yes" for match in font_flags), "all fonts embedded")
    lines.extend(["STATUS SELF-VERIFIED-NOT-INDEPENDENT", f"FINAL {final.name}", f"SHA256 {sha256(final)}"])
    transcript = ART / f"VERIFY-TRANSCRIPT-O{level}.txt"
    transcript.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
    print("\n".join(lines))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"VERIFY FAILED: {exc}", file=sys.stderr)
        raise
