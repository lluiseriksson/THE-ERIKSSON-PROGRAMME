from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

from pypdf import PdfReader, PdfWriter

ROOT = Path(__file__).resolve().parent
CFG = json.loads((ROOT / "package.json").read_text(encoding="utf-8"))
BUILD = ROOT / "artifacts" / "build"


def stop(message: str) -> None:
    print(f"ERROR: {message}", file=sys.stderr)
    raise SystemExit(1)


def run(command: list[str], cwd: Path, env: dict[str, str]) -> str:
    result = subprocess.run(command, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode != 0:
        stop(f"command failed ({result.returncode}): {' '.join(command)}\n{result.stdout}")
    return result.stdout


if BUILD.exists():
    shutil.rmtree(BUILD)
BUILD.mkdir(parents=True)
env = os.environ.copy()
env["SOURCE_DATE_EPOCH"] = "1785456000"
env["FORCE_SOURCE_DATE"] = "1"
source = ROOT / CFG["note_source"]
for pass_number in (1, 2):
    log = run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
               "-output-directory", str(BUILD), str(source)], ROOT, env)
    (BUILD / f"pdflatex-pass-{pass_number}.txt").write_text(log, encoding="utf-8")

note_pdf = BUILD / (source.stem + ".pdf")
log_text = (BUILD / (source.stem + ".log")).read_text(encoding="utf-8", errors="replace")
if "Overfull \\hbox" in log_text or "Overfull \\vbox" in log_text:
    stop("overfull box remains in compiled note")

writer = PdfWriter()
for segment in CFG["segments"]:
    reader = PdfReader(note_pdf if segment["path"] == "$NOTE" else ROOT / segment["path"])
    first, last = segment["pages"]
    if first < 1 or last > len(reader.pages) or first > last:
        stop(f"invalid segment range: {segment}")
    for page_number in range(first - 1, last):
        writer.add_page(reader.pages[page_number])
writer.add_metadata({
    "/Title": CFG["title"],
    "/Author": "Lluis Eriksson",
    "/Creator": "publication-audit deterministic package builder",
    "/Producer": "pypdf",
    "/CreationDate": "D:20260731000000+00'00'",
    "/ModDate": "D:20260731000000+00'00'",
})
final_pdf = ROOT / "artifacts" / CFG["output_pdf"]
with final_pdf.open("wb") as handle:
    writer.write(handle)
shutil.copyfile(note_pdf, ROOT / "artifacts" / CFG["note_pdf"])

digest = hashlib.sha256(final_pdf.read_bytes()).hexdigest()
pages = len(PdfReader(final_pdf).pages)
if pages != CFG["expected_pages"]:
    stop(f"page count {pages} != {CFG['expected_pages']}")
transcript = (
    f"BUILD PASS\noptimize={sys.flags.optimize}\n"
    f"pdf={CFG['output_pdf']}\nsha256={digest}\npages={pages}\n"
    "source_date_epoch=1785456000\noverfull=0\n"
)
(ROOT / "artifacts" / "BUILD-TRANSCRIPT.txt").write_text(transcript, encoding="utf-8")
print(transcript, end="")
