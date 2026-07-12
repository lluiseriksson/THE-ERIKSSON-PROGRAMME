import importlib.util
from pathlib import Path
import sys

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))
SPEC = importlib.util.spec_from_file_location(
    "positive_t_centered",
    ROOT/"scripts"/"surface_remainder_positive_t_centered.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_t_series_algebra_division_identity():
    a = [MOD.tjet(arb(2+i), arb(1-i)) for i in range(MOD.PREC)]
    product = MOD._smul(a, MOD._sinv(a))
    for index, value in enumerate(product):
        expected = arb(1) if index == 0 else arb(0)
        assert (value.v-expected).contains(0)
        assert value.d.contains(0)
        assert value.d2.contains(0)
        assert value.d3.contains(0)
        assert value.d4.contains(0)


def test_one_t_centered_cell_is_finite():
    ctx.prec = 100
    calibration = [arb(0) for _ in range(MOD.PREC)]
    values = MOD.centered_cell(
        arb("0.04975"), arb("2.9 +/- 0.001"),
        arb(0), arb("0.05"), arb(0), arb("0.05"), calibration)
    assert all(value.v.is_finite() and value.d.is_finite()
               and value.d2.is_finite() and value.d3.is_finite()
               and value.d4.is_finite()
               for row in values.values() for value in row)


def test_t_derivative_encloses_symmetric_cell_difference():
    ctx.prec = 140
    h = arb("1e-6")
    t = arb("2.9")
    calibration = [arb(0) for _ in range(MOD.PREC)]
    values = MOD.centered_cell(
        arb("0.04975"), MOD.spatial.hull(t-h, t+h),
        arb(0), arb("0.02"), arb(0), arb("0.02"), calibration)
    plus = MOD.spatial.centered_cell(
        arb("0.04975"), t+h, arb(0), arb("0.02"),
        arb(0), arb("0.02"), calibration)
    minus = MOD.spatial.centered_cell(
        arb("0.04975"), t-h, arb(0), arb("0.02"),
        arb(0), arb("0.02"), calibration)
    for name in values:
        finite = (plus[name][0]-minus[name][0])/(2*h)
        assert (values[name][0].d-arb(finite.mid())).contains(0)


def test_nonfinite_cells_have_forced_refinement_priority():
    values = {"KD": [MOD.TJet(arb("nan"), arb(0))]}
    weights = {("KD", 0): 1.0}
    assert MOD._priority_score(values, weights, arb("0.01")) == float("inf")


def test_taylor_tracks_are_assembled_separately(monkeypatch):
    centre = MOD.TJet(arb("1.0 +/- 0.01"), arb("0.2 +/- 0.01"), arb(0))
    box = MOD.TJet(arb("1 +/- 1"), arb("0 +/- 2"), arb("3 +/- 0.1"))
    calls = []

    def fake_track(delta, t_eval, tradius, perturbation, max_cells, seed_grid):
        calls.append(t_eval)
        return (centre if len(calls) == 1 else box), 4, [arb(0)]*MOD.PREC

    monkeypatch.setattr(MOD, "residual_track", fake_track)
    value, derivative, second, third, fourth, cells, _ = MOD.residual_box(
        arb("0.05"), arb("2.0"), arb("2 +/- 0.1"), arb(0), max_cells=4)
    assert len(calls) == 2
    assert cells == 8
    assert derivative.contains(arb("0.2"))
    assert second.contains(0)
    assert third.contains(0)
    assert fourth.contains(0)
    assert value.contains(arb("1"))
