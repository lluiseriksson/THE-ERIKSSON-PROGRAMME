import importlib.util
from pathlib import Path
import sys

import mpmath as mp
from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))
SPEC = importlib.util.spec_from_file_location(
    "delta0_moments", ROOT/"scripts"/"surface_remainder_delta0_moments.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_regular_moments_cross_delta_zero_and_contain_direct_samples():
    ctx.prec = 180
    mp.mp.dps = 80
    moments = MOD.regular_moment_integrands(
        arb("0.025 +/- 0.025"), arb("2.9"), arb(3), arb(2))
    for delta in (mp.mpf("0.0001"), mp.mpf("0.01"), mp.mpf("0.05")):
        direct = MOD.scalar_direct(
            delta, mp.mpf("2.9"), mp.mpf(3), mp.mpf(2))
        for name, value in direct.items():
            assert getattr(moments, name).contains(arb(str(value))), name


def test_regular_moments_are_finite_at_delta_zero():
    ctx.prec = 180
    moments = MOD.regular_moment_integrands(
        arb(0), arb("2.9"), arb(3), arb(2))
    assert all(value.is_finite() for value in moments.__dict__.values())


def test_full_plane_bilinear_zero_is_structural():
    ctx.prec = 180
    for t in (arb("0.6"), arb("1.5"), arb("2.9")):
        moments = MOD.delta0_plane_moments(t)
        ratio1 = moments.kf_over_delta/moments.kd
        ratio2 = moments.hdf_over_delta3/moments.hdd_over_delta2
        assert ratio1.overlaps(ratio2)
        assert MOD.delta0_bilinear_zero(t).contains(arb(0))
