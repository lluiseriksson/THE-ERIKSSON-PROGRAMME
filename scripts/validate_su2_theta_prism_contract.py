#!/usr/bin/env python3
"""Static contract checks for (9) Fabricante del prisma theta."""

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
LANE = ROOT / "YangMills" / "SU2ThetaPrism"
CHARTER = ROOT / "docs" / "SU2-THETA-PRISM-CONTRACT-CHARTER.md"
REVIEW = ROOT / "docs" / "SU2-THETA-PRISM-HYPOTHESIS-REVIEW.md"

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
    if re.search(r"^\s*(?:structure\s+\w+[^\n]*\n(?:.|\n)*?)?\s*\w+\s*:\s*[^\n]*(?:"
                 r"witnessNormSq[^\n]*=\s*3\s*/\s*4|"
                 r"thetaPairing[^\n]*=|"
                 r"beta\s*\^\s*4\s*/\s*512|"
                 r"Complete(?:U|V|Relative)Orthogonality)" , text):
        errors.append(f"{rel}: loaded field appears to restate a headline")

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

if errors:
    for error in errors:
        print(f"ERROR: {error}", file=sys.stderr)
    raise SystemExit(1)

print(f"PASS: checked {len(lean_files)} Lean files; loaded-hypothesis rule visible")

