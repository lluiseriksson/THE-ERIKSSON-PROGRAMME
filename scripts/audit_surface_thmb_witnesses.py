"""Audit the two-witness status of Theorem B's beta<=3 certificate.

This is deliberately a diagnostic gate.  It never promotes the theorem: the
mpmath and Arb transcripts must both be present, non-empty, and carry their
two-pass completion markers before the manuscript may call the result a
two-witness certificate.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
STD = ROOT / "scripts" / "certify_thmB_transcript.txt"
ARB = ROOT / "scripts" / "certify_thmB_arb_transcript.txt"


def read_text(path: Path) -> str:
    """Read a transcript regardless of the shell's UTF-16/UTF-8 capture."""
    data = path.read_bytes()
    for encoding in ("utf-8-sig", "utf-16", "utf-8"):
        try:
            return data.decode(encoding)
        except UnicodeDecodeError:
            pass
    raise UnicodeDecodeError("unknown", data, 0, 1, "unsupported transcript encoding")


def audit() -> list[str]:
    errors: list[str] = []
    if not STD.is_file() or not read_text(STD).strip():
        errors.append("mpmath transcript missing or empty")
    else:
        text = read_text(STD)
        if not re.search(r"pass 1[^\n]*CERTIFIED Crit < 0", text):
            errors.append("mpmath transcript lacks pass-1 completion marker")
        if not re.search(r"pass 2[^\n]*STABLE", text):
            errors.append("mpmath transcript lacks pass-2 stability marker")

    if not ARB.is_file() or not read_text(ARB).strip():
        errors.append("Arb transcript missing or empty")
    else:
        text = read_text(ARB)
        if not re.search(r"pass 1 \(Arb\):[^\n]*86 boxes", text):
            errors.append("Arb transcript lacks the 86-box pass-1 marker")
        if not re.search(r"pass 2 \(Arb\):[^\n]*STABLE", text):
            errors.append("Arb transcript lacks pass-2 stability marker")
    return errors


def main() -> int:
    errors = audit()
    if errors:
        for error in errors:
            print(f"THMB TWO-WITNESS BLOCKED: {error}")
        return 1
    print("THMB TWO-WITNESS PASS: mpmath and Arb transcripts are complete")
    return 0


if __name__ == "__main__":
    sys.exit(main())
