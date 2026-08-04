"""Candidate-only factored delta weight for narrow K4 bands.

The historical centred-delta design module is kept byte-for-byte stable for
its archived manifests.  New experiments may import this helper instead of
changing that dependency tree.
"""

from flint import arb

from surface_remainder_centered_delta_integrator_design import (
    BUDGETS,
    DELTA_FINAL,
)


def taylor_weight(lo: arb, hi: arb, endpoint: arb = DELTA_FINAL) -> arb:
    """Evaluate endpoint*(hi-lo)-(hi²-lo²)/2 without cancellation."""
    return (hi-lo) * (endpoint-(hi+lo)/2)


def single_box_fractions(totals: dict[str, arb], lo: arb, hi: arb) -> dict[str, arb]:
    weight = taylor_weight(lo, hi)
    return {
        name: 2*arb(value.abs_upper())*weight
        / (BUDGETS[name]*DELTA_FINAL**2)
        for name, value in totals.items()
    }
