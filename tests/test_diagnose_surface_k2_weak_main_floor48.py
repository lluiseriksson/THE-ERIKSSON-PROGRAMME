"""Static contracts for the floor-grid-48 diagnostic."""

import ast
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT/"scripts"/"diagnose_surface_k2_weak_main_floor48.py"


def test_floor48_diagnostic_has_no_float_literals() -> None:
    tree = ast.parse(SCRIPT.read_text(encoding="utf-8"))
    assert not [
        node for node in ast.walk(tree)
        if isinstance(node, ast.Constant) and isinstance(node.value, float)
    ]


def test_floor48_diagnostic_is_non_gate_and_fixed_grid() -> None:
    source = SCRIPT.read_text(encoding="utf-8")
    assert "GRID = 48" in source
    assert 'row["grid"] == 24' in source
    assert "validator.validate(lane)" in source
    assert "diagnostic only; theorem gates unchanged" in source
    assert "lower > old_lower" in source
