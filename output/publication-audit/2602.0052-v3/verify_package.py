from __future__ import annotations

import hashlib
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

from PIL import Image
from pypdf import PdfReader

ROOT = Path(__file__).resolve().parent
CFG = json.loads((ROOT / "package.json").read_text(encoding="utf-8"))
LOCK = json.loads((ROOT / "LOCK.json").read_text(encoding="utf-8"))
QA = ROOT / "artifacts" / "qa-render"
checks: list[str] = []


def fail(message: str) -> None:
    print(f"FAIL: {message}", file=sys.stderr)
    raise SystemExit(1)


def require(condition: bool, message: str) -> None:
    if not condition:
        fail(message)
    checks.append(message)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


for relative, expected in LOCK.items():
    require(sha(ROOT / relative) == expected, f"locked hash {relative}")

final_pdf = ROOT / "artifacts" / CFG["output_pdf"]
final_reader = PdfReader(final_pdf)
require(len(final_reader.pages) == CFG["expected_pages"], "final page count")
require(not final_reader.is_encrypted, "final PDF is not encrypted")

sheet = (ROOT / "SUBMISSION-ID.txt").read_text(encoding="utf-8")
abstract = sheet.split("ABSTRACT:\n", 1)[1].split("\n\nCOMMENTS:", 1)[0]
comments = sheet.split("COMMENTS:\n", 1)[1].split("\n\nCHANGE NOTE:", 1)[0]
require(len(re.findall(r"\b[\w'-]+\b", abstract)) < 400, "abstract under 400 words")
require(len(re.findall(r"\b[\w'-]+\b", comments)) < 100, "comments under 100 words")
require("DO NOT UPLOAD" in sheet and "REVIEW-PENDING" in sheet, "submission hold is explicit")

required = {
    "2602.0052": ["Lemma 6.2", "Lemma 6.3", "Nor do three", "not established"],
    "2602.0036": ["correct identity", "unfavourable sign", "not established"],
    "2602.0035": ["One symbol, two angles", "H-FACT", "not established"],
}
text = subprocess.run(["pdftotext", str(final_pdf), "-"], check=True,
                      text=True, encoding="utf-8", errors="replace",
                      stdout=subprocess.PIPE).stdout
for phrase in required[CFG["id"]]:
    require(phrase in text, f"required claim phrase: {phrase}")

if QA.exists():
    shutil.rmtree(QA)
QA.mkdir(parents=True)


def render(pdf: Path, label: str) -> list[Path]:
    target = QA / label
    target.mkdir()
    subprocess.run(["pdftoppm", "-r", "120", "-png", str(pdf), str(target / "page")],
                   check=True, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    pages = sorted(target.glob("page-*.png"))
    require(bool(pages), f"rendered {label}")
    return pages


def pixels(path: Path) -> tuple[tuple[int, int], bytes]:
    with Image.open(path) as image:
        rgb = image.convert("RGB")
        return rgb.size, rgb.tobytes()


final_pngs = render(final_pdf, "final")
cursor = 0
for index, segment in enumerate(CFG["segments"], start=1):
    source = ROOT / "artifacts" / CFG["note_pdf"] if segment["path"] == "$NOTE" else ROOT / segment["path"]
    source_pngs = render(source, f"segment-{index}")
    first, last = segment["pages"]
    for source_page in range(first - 1, last):
        require(pixels(final_pngs[cursor]) == pixels(source_pngs[source_page]),
                f"pixel identity final page {cursor + 1} / segment {index} page {source_page + 1}")
        cursor += 1
require(cursor == len(final_pngs), "all final pages assigned to frozen segments")

mode = f"O{sys.flags.optimize}"
transcript = (
    f"VERIFY PASS\nmode={mode}\nid={CFG['id']}v{CFG['version']}\n"
    f"pdf={CFG['output_pdf']}\nsha256={sha(final_pdf)}\npages={len(final_pngs)}\n"
    f"checks={len(checks)}\npixel_pages={cursor}\nstatus=SELF-VERIFIED; REVIEW-PENDING\n"
)
(ROOT / "artifacts" / f"VERIFY-TRANSCRIPT-{mode}.txt").write_text(transcript, encoding="utf-8")
print(transcript, end="")
