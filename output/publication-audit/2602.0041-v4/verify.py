#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

from PIL import Image, ImageChops
from pypdf import PdfReader

ROOT = Path(__file__).resolve().parent
ART = ROOT / "artifacts"
INPUT = ROOT / "inputs" / "2602.0041v3-public.pdf"
POPPLER = Path(r"C:\Users\lluis\.cache\codex-runtimes\codex-primary-runtime\dependencies\native\poppler\Library\bin")


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def main() -> int:
    level = sys.flags.optimize
    lines = [f"PYTHON_OPTIMIZE_LEVEL {level}"]

    def check(value: bool, label: str) -> None:
        if not value:
            raise RuntimeError(label)
        lines.append(f"PASS {label}")

    result = json.loads((ART / "build-result.json").read_text(encoding="utf-8"))
    final = ART / result["final_pdf"]
    check(final.is_file(), "final exists")
    check(sha(final) == result["final_sha256"], "final SHA")
    check(sha(INPUT) == "f67dea05d521ce5ea59caf79edca8038f0eb850b5c2256282394ca665c01afbb", "public v3 SHA")
    reader = PdfReader(str(final), strict=True)
    check(not reader.is_encrypted and len(reader.pages) == 12, "final unencrypted 12 pages")
    active = (ROOT / "src" / "front_note.tex").read_text(encoding="utf-8") + (ROOT / "SUBMISSION-ID.txt").read_text(encoding="utf-8")
    flat = re.sub(r"\s+", " ", active)
    for phrase in ("Conditional result only", "requires the cross-scale", "additionally requires the Dobrushin", "No unconditional weak-coupling mass gap", "preserved 11-page v3"):
        check(phrase in flat, f"scope phrase: {phrase}")
    check("as" + "sert " not in Path(__file__).read_text(encoding="utf-8"), "no assertion statements")
    qa = ART / f"qa-o{level}"
    final_dir, input_dir = qa / "final", qa / "input"
    final_dir.mkdir(parents=True, exist_ok=True)
    input_dir.mkdir(parents=True, exist_ok=True)
    for directory in (final_dir, input_dir):
        for stale in directory.glob("*.png"):
            stale.unlink()
    for pdf, directory in ((final, final_dir), (INPUT, input_dir)):
        run = subprocess.run([str(POPPLER / "pdftoppm.exe"), "-r", "120", "-png", str(pdf), str(directory / "page")], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        check(run.returncode == 0, f"render {pdf.name}")
    final_pages = sorted(final_dir.glob("*.png"))
    input_pages = sorted(input_dir.glob("*.png"))
    check(len(final_pages) == 12 and len(input_pages) == 11, "rendered page counts")
    for index, old in enumerate(input_pages):
        with Image.open(final_pages[index + 1]).convert("RGB") as a, Image.open(old).convert("RGB") as b:
            check(a.size == b.size and ImageChops.difference(a, b).getbbox() is None, f"final page {index + 2} pixel-equals public v3 page {index + 1}")
    fonts = subprocess.run(["pdffonts", str(final)], text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    check(fonts.returncode == 0 and not re.search(r"\bno\s+(?:yes|no)\s+(?:yes|no)\s+\d+", fonts.stdout), "font inventory readable and embedded")
    lines.extend(["STATUS SELF-VERIFIED-NOT-INDEPENDENT", f"FINAL {final.name}", f"SHA256 {sha(final)}"])
    (ART / f"VERIFY-TRANSCRIPT-O{level}.txt").write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
    print("\n".join(lines))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"VERIFY FAILED: {exc}", file=sys.stderr)
        raise
