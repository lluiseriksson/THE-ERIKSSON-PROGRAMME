from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "validate_surface_closure", ROOT / "scripts" / "validate_surface_closure.py"
)
assert SPEC and SPEC.loader
validator = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = validator
SPEC.loader.exec_module(validator)


def fixture(root: Path, *, sealed: bool = False, slot: bool = True) -> None:
    (root / "docs").mkdir(parents=True)
    (root / "papers" / "surface-complete").mkdir(parents=True)
    states = {gate: validator.TERMINAL[gate] for gate in validator.GATES}
    submission = "READY_FOR_CLAIM_AUDIT"
    if not sealed:
        states.update({"G0": "RERUN_AUDIT_IN_PROGRESS", "G1": "OPEN_DESIGN",
                       "G2": "OPEN_DESIGN", "G3": "LOCAL_ONLY",
                       "G4": "DESIGN_RATIFIED", "G5": "OPEN_CONSTANTS",
                       "G6": "BLOCKED"})
        submission = "DO_NOT_SUBMIT"
    rows = "\n".join(
        f"| {gate} | scope | `{states[gate]}` | evidence |"
        for gate in validator.GATES
    )
    (root / "docs" / "SURFACE-CLOSURE-GATES.md").write_text(
        f"**Submission state:** `{submission}`\n\n{rows}\n", encoding="utf-8"
    )
    manuscript = "theorem"
    if slot:
        manuscript += " [SLOT: seal completion] DO NOT SUBMIT"
    (root / "papers" / "surface-complete" / "surface_theorem_complete.tex").write_text(
        manuscript, encoding="utf-8"
    )
    (root / "README.md").write_text(
        "[gates](docs/SURFACE-CLOSURE-GATES.md)", encoding="utf-8"
    )


def test_repository_surface_closure_board_is_valid() -> None:
    assert validator.validate(ROOT) == []


def test_open_manuscript_cannot_be_marked_sealed(tmp_path: Path) -> None:
    fixture(tmp_path, sealed=True, slot=True)
    errors = validator.validate(tmp_path)
    assert any("open manuscript ink requires" in error for error in errors)


def test_seal_requires_every_upstream_gate_terminal(tmp_path: Path) -> None:
    fixture(tmp_path, sealed=True, slot=False)
    board = tmp_path / "docs" / "SURFACE-CLOSURE-GATES.md"
    board.write_text(
        board.read_text(encoding="utf-8").replace("| G3 | scope | `CERTIFIED` |",
                                                  "| G3 | scope | `LOCAL_ONLY` |"),
        encoding="utf-8",
    )
    errors = validator.validate(tmp_path)
    assert any("G6=SEALED requires G3=CERTIFIED" in error for error in errors)


def test_missing_gate_is_rejected(tmp_path: Path) -> None:
    fixture(tmp_path)
    board = tmp_path / "docs" / "SURFACE-CLOSURE-GATES.md"
    board.write_text("\n".join(
        line for line in board.read_text(encoding="utf-8").splitlines()
        if not line.startswith("| G4 |")
    ), encoding="utf-8")
    assert any("missing Surface closure gates: G4" in error
               for error in validator.validate(tmp_path))

