"""Contracts for the deterministic parallel weak-main runner."""

import ast
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT/"scripts"/"run_surface_k2_weak_main_covariance_parallel.py"


def test_parallel_runner_has_no_float_literals() -> None:
    tree = ast.parse(SCRIPT.read_text(encoding="utf-8"))
    assert not [
        node for node in ast.walk(tree)
        if isinstance(node, ast.Constant) and isinstance(node.value, float)
    ]


def test_parallel_runner_frozen_topology() -> None:
    source = SCRIPT.read_text(encoding="utf-8")
    assert "WORKERS = 12" in source
    assert '"grids": (24, 48)' in source
    assert '"grids": (24, 48, 96)' in source
    assert "as_completed(futures)" in source
    assert 'results.sort(key=lambda item: (item["di"], item["ti"]))' in source
    assert 'progress_path.open("x"' in source
    assert '"FAILROW"' in source
