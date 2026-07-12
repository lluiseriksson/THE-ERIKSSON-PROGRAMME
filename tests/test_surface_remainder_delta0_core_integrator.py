import importlib.util
from pathlib import Path
import sys

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))
SPEC = importlib.util.spec_from_file_location(
    "delta0_core",
    ROOT/"scripts"/"surface_remainder_delta0_core_integrator.py",
)
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_regular_delta0_core_integral_is_finite():
    ctx.prec = 120
    delta = MOD.hull(arb(0), arb(1)/100)
    values = MOD.integrate_core(delta, arb("2.9"), 4)
    assert set(values) == set(MOD.NAMES)
    assert all(value.is_finite() for value in values.values())


def test_phase_centered_delta0_core_integral_is_finite():
    ctx.prec = 120
    delta = MOD.hull(arb(0), arb(1)/100)
    values = MOD.integrate_core_centered(delta, arb("2.9"), 4)
    assert all(value.is_finite() for value in values.values())


def test_bilinear_centering_is_applied_before_integration():
    ctx.prec = 120
    delta, t = MOD.hull(arb(0), arb(1)/100), arb("2.9")
    c = (t/4).cos(); cc = 2*c**2-1
    calibration = -(2*cc+1)/(2*c)
    values = MOD.integrate_core_centered(
        delta, t, 4, calibration=calibration)
    assert set(values) == {"kd", "kn", "hdd_over_delta2", "gn"}
    assert all(value.is_finite() for value in values.values())


def test_fixed_endpoint_complement_is_finite():
    ctx.prec = 120
    delta, t = MOD.hull(arb(0), arb(1)/100), arb("2.9")
    c = (t/4).cos(); cc = 2*c**2-1
    calibration = -(2*cc+1)/(2*c)
    values = MOD.integrate_complement_centered(
        delta, t, 4, calibration=calibration)
    assert all(value.is_finite() for value in values.values())


def test_adaptive_bilinear_partition_is_finite():
    ctx.prec = 120
    delta, t = MOD.hull(arb(0), arb(1)/100), arb("2.9")
    values, effective = MOD.adaptive_bilinear_centered(
        delta, t, max_cells=64, seed_grid=2)
    assert effective <= 64
    assert all(value.is_finite() for value in values.values())
