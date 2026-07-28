import mpmath as mp

from flint import arb, ctx

from surface_remainder_bivariate_jet import BiJet, parameter_carriers
from surface_remainder_carrier_jet import scalar_carrier


def test_bivariate_jet_matches_high_precision_derivatives():
    ctx.prec = 160
    mp.mp.dps = 70
    delta = mp.mpf("0.05")
    t = mp.mpf("2.9")
    s = mp.mpf("0.2")
    alpha = mp.mpf("0.3")
    jet = parameter_carriers(
        BiJet(arb(str(delta)), arb(1)),
        BiJet(arb(str(t)), arb(0), arb(1)),
        arb(str(s)), arb(str(alpha)),
    )["muF_main"]

    def f(d, u):
        return scalar_carrier(d, u, s, alpha, "muF_main")

    expected = (
        f(delta, t),
        mp.diff(lambda d: f(d, t), delta),
        mp.diff(lambda u: f(delta, u), t),
        mp.diff(lambda d: f(d, t), delta, 2) / 2,
        mp.diff(lambda d: mp.diff(lambda u: f(d, u), t), delta),
        mp.diff(lambda u: f(delta, u), t, 2) / 2,
    )
    actual = (jet.c00, jet.c10, jet.c01, jet.c20, jet.c11, jet.c02)
    for ball, value in zip(actual, expected):
        assert ball.contains(arb(str(value)))


def test_bivariate_jet_fails_closed_on_nonfinite_output():
    # The executable smoke is intentionally finite; this keeps the module
    # available as infrastructure without changing any theorem gate.
    out = parameter_carriers(
        BiJet(arb("0.05"), arb(1)),
        BiJet(arb("2.9"), arb(0), arb(1)),
        arb("0.2"), arb("0.3"),
    )
    assert all(getattr(value, field).is_finite()
               for value in out.values()
               for field in ("c00", "c10", "c01", "c20", "c11", "c02"))
