"""Static and algebraic contracts for the weak main covariance route."""

import ast
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT/"scripts"/"certify_surface_k2_weak_main_covariance.py"


def test_weak_covariance_source_has_no_float_literals() -> None:
    tree = ast.parse(SCRIPT.read_text(encoding="utf-8"))
    assert not [
        node for node in ast.walk(tree)
        if isinstance(node, ast.Constant) and isinstance(node.value, float)
    ]


def test_centered_integrands_are_formed_before_integration() -> None:
    source = SCRIPT.read_text(encoding="utf-8")
    assert "centered = b_relative*d_weight-2*root*a_relative" in source
    assert '"gdd": h_prefactor*d_weight*centered*exponential' in source
    assert '"gdf": h_prefactor*f_weight*centered*exponential' in source
    assert "GRID_LADDER = (24, 48)" in source


def test_terminal_determinant_uses_four_integrated_moments() -> None:
    source = SCRIPT.read_text(encoding="utf-8")
    assert "core = core_moments(delta, t, grid)" in source
    assert 'moments["kd"]*moments["gdf"]' in source
    assert 'moments["kf"]*moments["gdd"]' in source
    assert "GDD = HDD-r0*KD,  GDF = HDF-r0*KF" in source


def test_positive_denominator_square_is_dependency_free() -> None:
    source = SCRIPT.read_text(encoding="utf-8")
    assert "denominator = positive_square(moments[\"kd\"])" in source
    assert ')/moments["kd"]**2' not in source
