import importlib.util
from pathlib import Path
import sys

import mpmath as mp
from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))
SPEC = importlib.util.spec_from_file_location(
    "delta0_geometry", ROOT/"scripts"/"surface_remainder_delta0_geometry.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_sinc_squared_entire_lane_contains_direct_values():
    ctx.prec = 160
    mp.mp.dps = 70
    enclosure = MOD.sinc_squared_y(MOD.hull(arb(0), arb("1.25")))
    for y in (mp.mpf(0), mp.mpf("0.1"), mp.mpf("0.7"), mp.mpf("1.25")):
        exact = mp.mpf(1) if y == 0 else mp.sin(mp.sqrt(y))**2/y
        assert enclosure.contains(arb(str(exact)))


def test_regular_geometry_crosses_delta_zero_and_contains_samples():
    ctx.prec = 160
    mp.mp.dps = 70
    t = arb("2.9")
    geometry = MOD.regular_geometry(
        MOD.hull(arb(0), arb(1)/20), t, arb(3), arb(2))
    for delta in (mp.mpf("0.0001"), mp.mpf("0.01"), mp.mpf("0.05")):
        direct = MOD.scalar_original(
            delta, mp.mpf("2.9"), mp.mpf(3), mp.mpf(2))
        for name, value in direct.items():
            assert getattr(geometry, name).contains(arb(str(value))), name


def test_exact_delta_zero_limits():
    ctx.prec = 160
    t, sigma, tau = arb("2.9"), arb(3), arb(2)
    got = MOD.regular_geometry(arb(0), t, sigma, tau)
    c = (t/4).cos(); cc = 2*c**2-1
    assert got.p_over_delta.contains(sigma**2/4)
    assert got.q_over_delta.contains(tau**2/4)
    assert got.phase.contains(-c*(sigma**2+tau**2)/2)
    assert got.f_over_delta.contains(-sigma**2*(2*cc+1))
    assert got.inv_z == 0
