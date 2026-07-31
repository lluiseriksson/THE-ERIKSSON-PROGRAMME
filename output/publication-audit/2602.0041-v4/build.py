#!/usr/bin/env python3
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
ART = ROOT / "artifacts"
JOB = "2602_0041_v4_front"


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def main() -> int:
    ART.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    env["SOURCE_DATE_EPOCH"] = "1785528000"
    command = ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", f"-jobname={JOB}", f"-output-directory={ART}", "front_note.tex"]
    transcript: list[str] = []
    for number in (1, 2):
        run = subprocess.run(command, cwd=SRC, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        transcript.append(f"=== PDFLATEX PASS {number} ===\n{run.stdout}")
        if run.returncode:
            raise RuntimeError(f"pdflatex pass {number} failed")
    log = (ART / f"{JOB}.log").read_text(encoding="utf-8", errors="replace")
    if "Overfull \\hbox" in log or "Overfull \\vbox" in log:
        raise RuntimeError("overfull box")
    front = ART / f"{JOB}.pdf"
    old = INPUTS / "2602.0041v3-public.pdf"
    writer = PdfWriter()
    writer.append(str(front))
    writer.append(str(old))
    writer.add_metadata({"/Title": "Uniform Log-Sobolev Inequality and Mass Gap for Lattice Yang-Mills Theory: A Conditional Reduction", "/Author": "Lluis Eriksson", "/Subject": "Version 4 retitling and scope correction"})
    provisional = ART / "2602.0041v4.pdf"
    with provisional.open("wb") as stream:
        writer.write(stream)
    digest = sha(provisional)
    pages = len(PdfReader(str(provisional)).pages)
    final = ART / f"2602.0041v4-{digest[:8]}-{pages}pp.pdf"
    if final.exists():
        final.unlink()
    provisional.replace(final)
    result = {"status": "BUILT-NOT-INDEPENDENTLY-AUDITED", "final_pdf": final.name, "final_sha256": digest, "pages": pages, "front_pages": len(PdfReader(str(front)).pages), "public_v3_pages": len(PdfReader(str(old)).pages), "public_v3_sha256": sha(old), "source_sha256": sha(SRC / "front_note.tex")}
    (ART / "build-result.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    transcript.append("=== BUILD RESULT ===\n" + json.dumps(result, indent=2))
    (ART / "BUILD-TRANSCRIPT.txt").write_text("\n\n".join(transcript) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"BUILD FAILED: {exc}", file=sys.stderr)
        raise
