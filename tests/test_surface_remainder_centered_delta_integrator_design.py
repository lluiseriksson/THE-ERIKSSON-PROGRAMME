from flint import arb, ctx

import surface_remainder_centered_delta_integrator_design as design
from surface_remainder_centered_delta_integrator_factored import (
    single_box_fractions as factored_single_box_fractions,
    taylor_weight as factored_taylor_weight,
)


def test_born_centered_delta_integral_is_finite():
    ctx.prec = 140
    totals, cells, fallbacks = design.adaptive_integral(
        arb("0.049"), arb("0.05"), max_cells=576)
    assert cells == 576
    assert 0 <= fallbacks <= cells
    assert totals.keys() == design.BUDGETS.keys()
    assert all(value.is_finite() for value in totals.values())
    # Finiteness is the born-cover contract; the strict endpoint budget is
    # tested by the frozen 1,152-cell design run, not this cheaper smoke.


def test_cell_budget_must_contain_born_partition():
    try:
        design.adaptive_integral(arb("0.049"), arb("0.05"), max_cells=575)
    except ValueError as exc:
        assert "born partition" in str(exc)
    else:
        raise AssertionError("undersized adaptive cover must be rejected")


def test_literal_fraction_restores_half_second_derivative_factor():
    lo, hi = arb("0.049"), arb("0.05")
    weight = design.taylor_weight(lo, hi)
    totals = {
        name: budget*design.DELTA_FINAL**2/(2*weight)
        for name, budget in design.BUDGETS.items()
    }
    fractions = design.single_box_fractions(totals, lo, hi)
    # The budgets are Arb balls created at module-import precision.  After
    # the integration smoke raises ``ctx.prec``, recomputing the algebra can
    # place the rounded ball microscopically to either side of one even
    # though the displayed formula is exactly one.  Test the normalization
    # (and, in particular, distinguish it from the erroneous factor 1/2)
    # without imposing a false dependency contract on those balls.
    tolerance = arb("1e-10")
    assert all(abs(value-arb(1)) < tolerance
               for value in fractions.values())


def test_taylor_weight_keeps_positive_width_on_narrow_box():
    lo = arb("0.0660")
    hi = arb("0.0661")
    weight = factored_taylor_weight(lo, hi)
    expected = (hi - lo) * (design.DELTA_FINAL - (hi + lo) / 2)
    assert weight > 0
    assert expected > 0
    assert weight.overlaps(expected)


def test_taylor_weight_is_zero_at_a_box_centred_on_endpoint():
    lo = design.DELTA_FINAL - arb("1e-5")
    hi = design.DELTA_FINAL + arb("1e-5")
    weight = factored_taylor_weight(lo, hi)
    assert abs(weight) < arb("1e-18")
