#!/usr/bin/env python3
"""Adversarial mechanical checks for the R30 replacement candidate."""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

import mpmath as mp
from PIL import Image, ImageChops
from pypdf import PdfReader


ROOT = Path(__file__).resolve().parent
ARTIFACTS = ROOT / "artifacts"
INPUTS = ROOT / "inputs"
SRC = ROOT / "src"
PDFTOPPM = Path(
    r"C:\Users\lluis\.cache\codex-runtimes\codex-primary-runtime"
    r"\dependencies\native\poppler\Library\bin\pdftoppm.exe"
)


class Failure(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Failure(message)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def render(pdf: Path, directory: Path) -> list[Path]:
    directory.mkdir(parents=True, exist_ok=True)
    for stale in directory.glob("page-*.png"):
        stale.unlink()
    completed = subprocess.run(
        [str(PDFTOPPM), "-r", "120", "-png", str(pdf), str(directory / "page")],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    require(completed.returncode == 0, f"render failed for {pdf}: {completed.stderr}")
    return sorted(directory.glob("page-*.png"))


def pixel_equal(left: Path, right: Path) -> bool:
    with Image.open(left).convert("RGB") as a, Image.open(right).convert("RGB") as b:
        return a.size == b.size and ImageChops.difference(a, b).getbbox() is None


def main() -> int:
    optimize_level = sys.flags.optimize
    lines: list[str] = [f"PYTHON_OPTIMIZE_LEVEL {optimize_level}"]

    def check(condition: bool, label: str) -> None:
        require(condition, label)
        lines.append(f"PASS {label}")

    build = json.loads((ARTIFACTS / "build-result.json").read_text(encoding="utf-8"))
    final = ARTIFACTS / build["final_pdf"]
    erratum = ARTIFACTS / build["erratum_pdf"]
    provenance = INPUTS / "OBJECT-PROVENANCE-f3c2e1cb-4pp.pdf"
    public_v2 = INPUTS / "2602.0033v2-public.pdf"
    tex = SRC / "erratum_2602_0033.tex"
    submission = ROOT / "SUBMISSION-ID.txt"

    check(final.is_file(), "final PDF exists")
    check(sha256(final) == build["final_pdf_sha256"], "final PDF SHA matches build result")
    final_reader = PdfReader(str(final))
    check(not final_reader.is_encrypted, "final PDF is not encrypted")
    check(len(final_reader.pages) == 25, "final PDF has 25 pages")
    check(len(PdfReader(str(erratum)).pages) == 13, "erratum has 13 pages")
    check(len(PdfReader(str(provenance)).pages) == 4, "provenance has 4 pages")
    check(len(PdfReader(str(public_v2)).pages) == 8, "preserved public v2 has 8 pages")
    check(
        sha256(provenance) == "f3c2e1cb9ffcc1a1c0f66f5da96fa415248480eebd03f7abd2d93458a5b5cd01",
        "provenance input SHA is frozen",
    )
    check(
        sha256(public_v2) == "91a7d95e1decc1771c548533748916d9941a77f02937fddf90fb13e348730bfe",
        "public v2 input SHA is frozen",
    )

    text = tex.read_text(encoding="utf-8")
    active = text + "\n" + submission.read_text(encoding="utf-8")
    active_flat = re.sub(r"\s+", " ", active)
    for forbidden in (
        "the normalisation quotient divided by",
        "The family above has $d_0=1$",
        "the implicit relative-error constant must be uniform in g",
    ):
        check(forbidden not in active, f"forbidden phrase absent: {forbidden}")
    for required in (
        "actual finite-$M$ first-excited contributions",
        "A_n(M)e^{-m_n(M)M}",
        "A_{n+1}(M/2)e^{-m_{n+1}(M/2)M/2}",
        "necessary but not sufficient",
        "normalisation error",
        "original fixed-gap exact-trace family of Section 2",
        "chosen explicit bound",
    ):
        check(required in active_flat, f"required phrase present: {required}")
    assert_token = "as" + "sert "
    check(assert_token not in Path(__file__).read_text(encoding="utf-8"), "verifier has no assertion statements")

    mp.mp.dps = 100
    for m_value in (4, 8, 16, 24, 64, 256):
        M = mp.mpf(m_value)
        a = mp.mpf(1) / 3
        b = mp.mpf(1)
        a_m = a + 1 / mp.sqrt(M)
        b_half = b + 1 / mp.sqrt(M / 2)
        x = mp.exp(-a_m * M)
        y = mp.exp(-b_half * M / 2)
        q = (1 + x) / (1 + y)
        old_ratio = abs(q - 1) / mp.exp(-a * M)
        new_ratio = abs(q - 1) / (x + y)
        trace_n = 1 + x
        trace_next = q * (1 + y)
        check(mp.almosteq(trace_n, trace_next), f"positivity example exact trace identity M={m_value}")
        if m_value >= 64:
            check(old_ratio < mp.mpf("1e-3"), f"old limiting-scale ratio tends to zero M={m_value}")
            check(new_ratio > mp.mpf("0.9"), f"new finite-M condition rejects example M={m_value}")
    check(mp.mpf(1) != 2 * (mp.mpf(1) / 3), "positivity example violates limiting doubling")

    qa = ARTIFACTS / f"qa-render-o{optimize_level}"
    final_pages = render(final, qa / "final")
    provenance_pages = render(provenance, qa / "provenance")
    v2_pages = render(public_v2, qa / "public-v2")
    check(len(final_pages) == 25, "render produced all 25 final pages")
    for index, reference in enumerate(provenance_pages):
        check(pixel_equal(final_pages[13 + index], reference), f"page {14 + index} pixel-equals provenance page {index + 1}")
    for index, reference in enumerate(v2_pages):
        check(pixel_equal(final_pages[17 + index], reference), f"page {18 + index} pixel-equals public v2 page {index + 1}")

    lines.append("STATUS SELF-VERIFIED-NOT-INDEPENDENT")
    lines.append(f"FINAL {final.name}")
    lines.append(f"SHA256 {sha256(final)}")
    transcript = ARTIFACTS / f"VERIFY-TRANSCRIPT-O{optimize_level}.txt"
    transcript.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
    print("\n".join(lines))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"VERIFY FAILED: {exc}", file=sys.stderr)
        raise
