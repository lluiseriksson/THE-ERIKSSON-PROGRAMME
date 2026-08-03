#!/usr/bin/env python3
"""Build the R30 erratum bundle without mutating R29 or the public v2 input."""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

from pypdf import PdfReader, PdfWriter


ROOT = Path(__file__).resolve().parent
SRC = ROOT / "src"
INPUTS = ROOT / "inputs"
ARTIFACTS = ROOT / "artifacts"
TEX = SRC / "erratum_2602_0033.tex"
JOB = "erratum_2602_0033_r30"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def run(argv: list[str], *, cwd: Path, env: dict[str, str]) -> str:
    completed = subprocess.run(
        argv, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True
    )
    if completed.returncode:
        raise RuntimeError(f"command failed ({completed.returncode}): {argv!r}\n{completed.stdout}")
    return completed.stdout


def main() -> int:
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    env["SOURCE_DATE_EPOCH"] = "1785528000"  # 2026-07-31T20:00:00Z
    transcript = []
    latex = "pdflatex"
    command = [
        latex,
        "-interaction=nonstopmode",
        "-halt-on-error",
        f"-jobname={JOB}",
        f"-output-directory={ARTIFACTS}",
        TEX.name,
    ]
    for pass_number in (1, 2):
        output = run(command, cwd=SRC, env=env)
        transcript.append(f"=== PDFLATEX PASS {pass_number} ===\n{output}")

    log = (ARTIFACTS / f"{JOB}.log").read_text(encoding="utf-8", errors="replace")
    if "Overfull \\hbox" in log or "Overfull \\vbox" in log:
        raise RuntimeError("LaTeX overfull box detected")

    erratum = ARTIFACTS / f"{JOB}.pdf"
    provenance = INPUTS / "OBJECT-PROVENANCE-f3c2e1cb-4pp.pdf"
    public_v2 = INPUTS / "2602.0033v2-public.pdf"
    writer = PdfWriter()
    writer.append(str(erratum))
    writer.append(str(provenance))
    writer.append(str(public_v2))
    writer.add_metadata(
        {
            "/Title": "The Yang-Mills Mass Gap on the Lattice: A Conditional Synthesis - R30 replacement bundle",
            "/Author": "Lluis Eriksson",
            "/Subject": "Erratum, provenance, and preserved public v2",
        }
    )
    provisional = ARTIFACTS / "2602.0033v3-R30.pdf"
    with provisional.open("wb") as stream:
        writer.write(stream)

    pages = len(PdfReader(str(provisional)).pages)
    digest = sha256(provisional)
    final = ARTIFACTS / f"2602.0033v3-R30-{digest[:8]}-{pages}pp.pdf"
    if final.exists():
        final.unlink()
    provisional.replace(final)
    for stale in ARTIFACTS.glob("2602.0033v3-R30-*-*pp.pdf"):
        if stale != final:
            stale.unlink()

    manifest = {
        "status": "BUILT-NOT-AUDITED",
        "final_pdf": final.name,
        "final_pdf_sha256": digest,
        "final_pdf_pages": pages,
        "erratum_pdf": erratum.name,
        "erratum_pdf_sha256": sha256(erratum),
        "erratum_pdf_pages": len(PdfReader(str(erratum)).pages),
        "provenance_pdf_sha256": sha256(provenance),
        "public_v2_pdf_sha256": sha256(public_v2),
        "source_tex_sha256": sha256(TEX),
    }
    (ARTIFACTS / "build-result.json").write_text(
        json.dumps(manifest, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    transcript.append("=== BUILD RESULT ===\n" + json.dumps(manifest, indent=2))
    (ARTIFACTS / "BUILD-TRANSCRIPT.txt").write_text(
        "\n\n".join(transcript) + "\n", encoding="utf-8", newline="\n"
    )
    print(json.dumps(manifest, indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"BUILD FAILED: {exc}", file=sys.stderr)
        raise
