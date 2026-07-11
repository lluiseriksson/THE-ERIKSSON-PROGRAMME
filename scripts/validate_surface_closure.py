"""Validate the independent gate board for the Surface Theorem paper."""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
GATES = tuple(f"G{i}" for i in range(7))
TERMINAL = {
    "G0": "PASS",
    "G1": "CERTIFIED",
    "G2": "CERTIFIED",
    "G3": "CERTIFIED",
    "G4": "CERTIFIED",
    "G5": "CERTIFIED",
    "G6": "SEALED",
}
ROW = re.compile(r"^\| (G[0-6]) \|.*?\| `([^`]+)` \|", re.MULTILINE)
SUBMISSION = re.compile(r"^\*\*Submission state:\*\* `([^`]+)`", re.MULTILINE)


def validate(root: Path = ROOT) -> list[str]:
    errors: list[str] = []
    board_path = root / "docs" / "SURFACE-CLOSURE-GATES.md"
    manuscript_path = root / "papers" / "surface-complete" / "surface_theorem_complete.tex"
    readme_path = root / "README.md"
    for path in (board_path, manuscript_path, readme_path):
        if not path.is_file():
            errors.append(f"missing Surface closure file: {path.relative_to(root)}")
    if errors:
        return errors

    board = board_path.read_text(encoding="utf-8")
    manuscript = manuscript_path.read_text(encoding="utf-8")
    readme = readme_path.read_text(encoding="utf-8")
    rows = ROW.findall(board)
    states: dict[str, str] = {}
    for gate, state in rows:
        if gate in states:
            errors.append(f"duplicate Surface closure gate: {gate}")
        states[gate] = state
    missing = sorted(set(GATES) - set(states))
    extra = sorted(set(states) - set(GATES))
    if missing:
        errors.append(f"missing Surface closure gates: {', '.join(missing)}")
    if extra:
        errors.append(f"unknown Surface closure gates: {', '.join(extra)}")

    submission_match = SUBMISSION.search(board)
    submission = submission_match.group(1) if submission_match else None
    if submission is None:
        errors.append("Surface closure board has no submission state")
    if "docs/SURFACE-CLOSURE-GATES.md" not in readme:
        errors.append("README.md does not link the Surface closure board")

    open_ink = (
        "[SLOT" in manuscript
        or "DO NOT SUBMIT" in manuscript
        or "one open obligation" in manuscript
        or "named open hypothesis" in manuscript
    )
    if open_ink:
        if submission != "DO_NOT_SUBMIT":
            errors.append("open manuscript ink requires submission state DO_NOT_SUBMIT")
        if states.get("G6") != "BLOCKED":
            errors.append("open manuscript ink requires G6=BLOCKED")

    if states.get("G6") == "SEALED":
        for gate in GATES[:-1]:
            if states.get(gate) != TERMINAL[gate]:
                errors.append(
                    f"G6=SEALED requires {gate}={TERMINAL[gate]}, "
                    f"found {states.get(gate)!r}"
                )
        if submission != "READY_FOR_CLAIM_AUDIT":
            errors.append("G6=SEALED requires READY_FOR_CLAIM_AUDIT")
    return sorted(set(errors))


def main() -> int:
    errors = validate()
    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        return 1
    print("Surface closure gate board OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())

