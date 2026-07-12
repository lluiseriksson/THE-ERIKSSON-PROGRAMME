import importlib.util
from pathlib import Path
import sys

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))


def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT/"scripts"/(name+".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


MOD = load("surface_remainder_positive_physical_spatial3")
BASE = load("surface_remainder_positive_physical_series_design")


def test_cubic_jet_reproduces_existing_value_gradient_hessian():
    ctx.prec = 140
    delta, t, s, a = arb("0.04975"), arb("2.9"), arb("0.4"), arb("0.3")
    values3, phase3 = MOD.physical_moment_parts(
        delta, t, MOD.variable_x(s), MOD.variable_y(a))
    values2, phase2 = BASE.physical_moment_parts(
        delta, t, BASE.Dual(s, arb(1)), BASE.Dual(a, arb(0), arb(1)))
    for series3, series2 in list(zip(values3.values(), values2.values())) \
            +[(phase3, phase2)]:
        for jet3, dual2 in zip(series3, series2):
            comparisons = (
                (jet3.get(0, 0), dual2.v),
                (jet3.get(1, 0), dual2.x),
                (jet3.get(0, 1), dual2.y),
                (2*jet3.get(2, 0), dual2.xx),
                (jet3.get(1, 1), dual2.xy),
                (2*jet3.get(0, 2), dual2.yy),
            )
            assert all((left-right).contains(0) for left, right in comparisons)


def test_linear_moments_match_existing_closed_forms():
    ctx.prec = 140
    g, width = arb("-0.7"), arb("0.15")
    assert (MOD.linear_moment(g, width, 0)
            -BASE.linear_integral(g, width)).contains(0)
    assert (MOD.linear_moment(g, width, 1)
            -BASE.linear_first_moment(g, width)).contains(0)
    assert MOD.linear_moment(arb(0), width, 2).contains(width**3/12)


def test_one_cubic_spatial_cell_is_finite():
    ctx.prec = 140
    calibration = [arb(0) for _ in range(MOD.PREC)]
    values = MOD.centered_cell(
        arb("0.04975"), arb("2.9"), arb(0), arb("0.05"),
        arb(0), arb("0.05"), calibration)
    assert all(value.is_finite() for row in values.values() for value in row)
