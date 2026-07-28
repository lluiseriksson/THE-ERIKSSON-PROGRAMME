from __future__ import annotations

import sys
from pathlib import Path

from flint import acb, arb, ctx


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))

import probe_surface_k2_fixed_square_complex_supremum as probe  # noqa: E402


def test_entire_p_series_matches_real_closed_form() -> None:
    ctx.prec = 180
    delta = arb("0.001")
    coordinate = arb("1.25")
    actual = probe.p_over_delta(acb(delta), coordinate)
    expected = (delta.sqrt()*coordinate/2).sin()**2/delta
    assert actual.real.overlaps(expected)
    assert actual.imag.contains(0)


def test_complex_supremum_contract_is_fixed() -> None:
    assert probe.RHO.overlaps(arb(17)/2000)
    assert probe.DELTA_MAX.overlaps(arb(1)/1000)
    assert probe.LADDER == ((12, 16), (24, 32), (48, 64))
    available, multiplier, required_m = probe.cauchy_budget()
    assert available > 0
    assert multiplier > 0
    assert required_m > 0
