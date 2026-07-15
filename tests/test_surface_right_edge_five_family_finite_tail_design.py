from flint import arb, ctx

import surface_right_edge_five_family_finite_tail_design as finite_tail
import surface_right_edge_five_family_tail_design as halfline_tail


def test_finite_tail_geometry_and_budgets():
    ctx.prec = 140
    finite_tail.verify_geometry()
    values = finite_tail.budgets()
    ceilings = (
        arb("0.005804"), arb("0.004262"), arb("0.002151"),
        arb("0.006770"), arb("0.005300"),
    )
    assert all(value > 0 and value < ceiling
               for value, ceiling in zip(values, ceilings))
    assert (finite_tail.crude_chain_constant(5)
            > halfline_tail.crude_chain_constant(5))


def test_local_tail_budgets_tighten_above_beta20():
    global_values = finite_tail.budgets()
    local_values = finite_tail.budgets(arb(1)/30)
    assert all(local < global_value
               for local, global_value in zip(local_values, global_values))
