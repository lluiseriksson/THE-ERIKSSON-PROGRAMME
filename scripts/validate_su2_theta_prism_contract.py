#!/usr/bin/env python3
"""Syntactic contract guards for the SU(2) theta-prism artefact.

This script deliberately makes no claim of semantic honesty.  It rejects
specific headline-bearing field shapes and leaves participation to Lean and
the recorded manual review.
"""

import argparse
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
LANE = ROOT / "YangMills" / "SU2ThetaPrism"
CHARTER = ROOT / "docs" / "SU2-THETA-PRISM-CONTRACT-CHARTER.md"
REVIEW = ROOT / "docs" / "SU2-THETA-PRISM-HYPOTHESIS-REVIEW.md"

HEADLINE_FIELD_PATTERNS = (
    re.compile(
        r"\b[A-Za-z_][A-Za-z0-9_']*\s*:\s*"
        r"(?:[A-Za-z_][A-Za-z0-9_']*\.)*witnessNormSq\s*=\s*"
        r"(?:\(\s*)?3\s*/\s*4(?:\s*\))?",
        flags=re.MULTILINE,
    ),
    re.compile(
        r"\b[A-Za-z_][A-Za-z0-9_']*\s*:\s*"
        r"(?:\(\s*)?3\s*/\s*4(?:\s*\))?\s*=\s*"
        r"(?:[A-Za-z_][A-Za-z0-9_']*\.)*witnessNormSq",
        flags=re.MULTILINE,
    ),
    re.compile(
        r"\b[A-Za-z_][A-Za-z0-9_']*\s*:\s*"
        r"(?:[A-Za-z_][A-Za-z0-9_']*\.)*"
        r"Complete(?:U|V|Relative)Orthogonality\b",
        flags=re.MULTILINE,
    ),
)


def headline_field_errors(text: str, label: str) -> list[str]:
    collapsed = re.sub(r"\s+", " ", text)
    return [
        f"{label}: syntactic headline guard rejected a result-bearing field"
        for pattern in HEADLINE_FIELD_PATTERNS
        if pattern.search(collapsed)
    ]


def validate_lane() -> list[str]:
    errors: list[str] = []
    lean_files = sorted(LANE.glob("*.lean"))
    if not lean_files:
        errors.append("no Lean files found in the task lane")

    for path in lean_files:
        text = path.read_text(encoding="utf-8")
        rel = path.relative_to(ROOT)
        for forbidden in ("sorry", "admit", "sorryAx"):
            if re.search(rf"\b{re.escape(forbidden)}\b", text):
                errors.append(f"{rel}: forbidden token {forbidden}")
        if re.search(r"^\s*axiom\b", text, flags=re.MULTILINE):
            errors.append(f"{rel}: project axiom declaration")
        if "YangMills.OS.ReflectionSplitting" in text:
            errors.append(f"{rel}: forbidden continuous ReflectionSplitting import")
        errors.extend(headline_field_errors(text, str(rel)))

    charter_text = CHARTER.read_text(encoding="utf-8") if CHARTER.exists() else ""
    if "(9) Fabricante del prisma theta" not in charter_text:
        errors.append("charter: missing canonical task name")
    if re.search(r"\(9[a-zA-Z]+\)", charter_text):
        errors.append("charter: alternate task number found")
    if "Loaded-hypothesis rule" not in charter_text:
        errors.append("charter: missing loaded-hypothesis rule")

    review_text = REVIEW.read_text(encoding="utf-8") if REVIEW.exists() else ""
    for marker in ("Technical input", "Artefact lemmas used", "Headline derived"):
        if marker not in review_text:
            errors.append(f"manual review: missing column {marker!r}")
    if "PENDING" in review_text:
        errors.append("manual review: unresolved PENDING participation row")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--probe-text",
        type=Path,
        help="validate one synthetic Lean snippet for mutation testing",
    )
    args = parser.parse_args()
    if args.probe_text is not None:
        errors = headline_field_errors(
            args.probe_text.read_text(encoding="utf-8"), str(args.probe_text)
        )
        checked = "one mutation probe"
    else:
        errors = validate_lane()
        checked = f"{len(sorted(LANE.glob('*.lean')))} Lean files"

    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    print(f"PASS: syntactic headline guard checked {checked}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
