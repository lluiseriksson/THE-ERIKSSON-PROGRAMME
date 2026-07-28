"""Strict final-seal audit for the Surface Theorem manuscript.

This is intentionally stricter than ``validate_surface_closure.py``.  It is
an executable release gate: a partial/candidate board must fail rather than
being mistaken for a finished theorem.  No gate is promoted by this script;
it only checks that the authoritative state already records all required
terminal evidence.
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BOARD = ROOT / "docs" / "SURFACE-CLOSURE-GATES.md"
MANUSCRIPT = ROOT / "papers" / "surface-complete" / "surface_theorem_complete.tex"
PDF = ROOT / "papers" / "surface-complete" / "surface_theorem_complete.pdf"
LOG = ROOT / "papers" / "surface-complete" / "surface_theorem_complete.log"
BUILD_MANIFEST = ROOT / "docs" / "SURFACE-FINAL-BUILD-20260728.json"
GATES = tuple(f"G{i}" for i in range(7))
ROW = re.compile(r"^\| (G[0-6]) \|.*?\| `([^`]+)` \|", re.MULTILINE)
SUBMISSION = re.compile(
    r"^\*\*Submission state:\*\* `([^`]+)`", re.MULTILINE
)


def canonical_text_sha256(path: Path) -> str:
    """Hash UTF-8 text after the repository's explicit LF normalization."""
    text = path.read_text(encoding="utf-8")
    return hashlib.sha256(text.replace("\r\n", "\n").encode("utf-8")).hexdigest()


def audit() -> list[str]:
    errors: list[str] = []
    if not BOARD.is_file():
        return ["missing closure board"]
    if not MANUSCRIPT.is_file():
        errors.append("missing authoritative manuscript")
    board = BOARD.read_text(encoding="utf-8")
    row_matches = ROW.findall(board)
    rows = dict(row_matches)
    if len(row_matches) != len(GATES):
        errors.append(
            f"closure board must contain exactly seven gate rows, found "
            f"{len(row_matches)}"
        )
    for gate in GATES:
        if sum(found_gate == gate for found_gate, _ in row_matches) != 1:
            errors.append(f"closure board must contain exactly one {gate} row")
    expected = {
        "G0": "PASS",
        "G1": "REMOVED_FROM_TERMINAL_PAPER",
        "G2": "CERTIFIED",
        "G3": "CERTIFIED",
        "G4": "CERTIFIED",
        "G5": "CERTIFIED",
        "G6": "SEALED",
    }
    for gate in GATES:
        if rows.get(gate) != expected[gate]:
            errors.append(f"{gate} requires {expected[gate]}, found {rows.get(gate)!r}")
    submission = SUBMISSION.search(board)
    if not submission or submission.group(1) != "READY_FOR_CLAIM_AUDIT":
        errors.append("submission state is not READY_FOR_CLAIM_AUDIT")
    if MANUSCRIPT.is_file():
        text = MANUSCRIPT.read_text(encoding="utf-8")
        forbidden = {
            "[SLOT": "unresolved [SLOT] marker",
            "DO NOT SUBMIT": "DO_NOT_SUBMIT manuscript banner",
            "pending rows": "pending relay language",
            "number pending": "pending bibliography identifier",
            "otherwise open": "obsolete global-open language",
            "remains conditional": "obsolete conditional-relay language",
            "open hypothesis": "open-hypothesis language",
            r"\emph{amber}": "amber evidence label",
        }
        folded = text.casefold()
        for needle, message in forbidden.items():
            if needle.casefold() in folded:
                errors.append(message)
        labels = set(re.findall(r"\\label\{([^}]+)\}", text))
        refs = set(
            re.findall(
                r"\\(?:ref|eqref|autoref)\{([^}]+)\}",
                text,
            )
        )
        missing_refs = sorted(refs - labels)
        if missing_refs:
            errors.append(
                "undefined manuscript references: " + ", ".join(missing_refs)
            )
        bibitems = set(re.findall(r"\\bibitem\{([^}]+)\}", text))
        cited = {
            key.strip()
            for group in re.findall(r"\\cite(?:\[[^\]]*\])?\{([^}]+)\}", text)
            for key in group.split(",")
        }
        missing_citations = sorted(cited - bibitems)
        if missing_citations:
            errors.append(
                "undefined bibliography keys: " + ", ".join(missing_citations)
            )
        if r"\begin{theorem}[the Surface Theorem]" not in text:
            errors.append("terminal Surface Theorem statement missing")
    if not PDF.is_file():
        errors.append("missing compiled final PDF")
    elif PDF.stat().st_size < 100_000 or not PDF.read_bytes().startswith(b"%PDF"):
        errors.append("compiled PDF is absent or implausibly small")
    if not BUILD_MANIFEST.is_file():
        errors.append("missing final build manifest")
    elif MANUSCRIPT.is_file() and PDF.is_file():
        try:
            build = json.loads(BUILD_MANIFEST.read_text(encoding="utf-8"))
            expected_tex = canonical_text_sha256(MANUSCRIPT)
            expected_pdf = hashlib.sha256(PDF.read_bytes()).hexdigest()
            if build.get("tex_sha256") != expected_tex:
                errors.append("final build manifest TeX hash mismatch")
            if build.get("pdf_sha256") != expected_pdf:
                errors.append("final build manifest PDF hash mismatch")
            if build.get("engine") != "pdfTeX" or build.get("passes", 0) < 2:
                errors.append("final build manifest lacks two pdfTeX passes")
            if build.get("fatal_errors") != 0:
                errors.append("final build manifest records a fatal error")
            if build.get("undefined_references") != 0:
                errors.append("final build manifest records undefined references")
            if build.get("undefined_citations") != 0:
                errors.append("final build manifest records undefined citations")
        except (OSError, json.JSONDecodeError, TypeError) as exc:
            errors.append(f"invalid final build manifest: {exc}")
    if LOG.is_file():
        log = LOG.read_text(encoding="utf-8", errors="replace")
        if "Fatal error occurred" in log or "!  ==> Fatal error" in log:
            errors.append("LaTeX log contains a fatal error")
        if "There were undefined references" in log:
            errors.append("LaTeX log contains undefined references")
        if "There were undefined citations" in log:
            errors.append("LaTeX log contains undefined citations")
    if not errors:
        try:
            scripts = ROOT / "scripts"
            if str(scripts) not in sys.path:
                sys.path.insert(0, str(scripts))
            import audit_surface_terminal_prerequisites as terminal_prerequisites

            prerequisites = terminal_prerequisites.audit()
            if prerequisites.get("promotion") != "TERMINAL_PREREQUISITES_PROVED":
                errors.append("terminal prerequisite audit did not promote")
        except Exception as exc:
            errors.append(f"terminal prerequisite audit failed: {exc}")
    if not errors:
        try:
            scripts = ROOT / "scripts"
            if str(scripts) not in sys.path:
                sys.path.insert(0, str(scripts))
            import audit_surface_g2_terminal_cover as g2_terminal

            g2 = g2_terminal.audit()
            if g2.get("promotion") != "G2_TERMINAL_COVER_PROVED":
                errors.append("G2 terminal domain audit did not promote")
        except Exception as exc:
            errors.append(f"G2 terminal domain audit failed: {exc}")
    if not errors:
        try:
            scripts = ROOT / "scripts"
            if str(scripts) not in sys.path:
                sys.path.insert(0, str(scripts))
            import audit_surface_closed_form_anchors as closed_form_anchors

            anchors = closed_form_anchors.audit()
            if anchors.get("promotion") != "CLOSED_FORM_ANCHORS_PROVED":
                errors.append("closed-form anchor audit did not promote")
        except Exception as exc:
            errors.append(f"closed-form anchor audit failed: {exc}")
    return sorted(set(errors))


def main() -> int:
    errors = audit()
    if errors:
        for error in errors:
            print(f"FINAL-SEAL BLOCKED: {error}")
        return 1
    print("FINAL-SEAL PASS: terminal gates, manuscript, and PDF are present")
    return 0


if __name__ == "__main__":
    sys.exit(main())
