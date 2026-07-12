from fractions import Fraction

from flint import arb

import surface_remainder_delta0_extension_probe as mod


def test_exact_fraction_conversion():
    assert mod.aq(Fraction(3, 1000)).overlaps(arb("0.003"))


def test_extension_module_does_not_mutate_sealed_lane():
    assert mod.sealed.DELTA_MAX == Fraction(1, 1000)


def test_parallel_integral_overlaps_sequential_small_grid():
    lane = mod.hull(arb(0), arb("0.001"))
    t = mod.hull(arb("1"), arb("1.02"))
    sequential_rows = mod.integrate_coefficients(t, grid=4, base=lane)
    sequential = {name: mod.arb_series(row, mod.PREC)
                  for name, row in sequential_rows.items()}
    parallel = mod.parallel_integrate_coefficients(lane, t, grid=4)
    for name in sequential:
        assert all(a.overlaps(b) for a, b in zip(
            sequential[name].coeffs(), parallel[name].coeffs()))
