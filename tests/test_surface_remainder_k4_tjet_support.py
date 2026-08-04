from flint import arb, ctx

from surface_remainder_centered_delta_carrier import main_carriers, mirror_carriers
from surface_remainder_tjet import tjet


def test_k4_carriers_preserve_tjet_derivatives():
    ctx.prec = 100
    t = tjet(arb("2.9"), 1, 0, 0, 0)
    delta = tjet(arb("0.04"))
    main = main_carriers(delta, t, arb("0.2"), arb("0.3"))
    mirror = mirror_carriers(delta, t, arb("0.2"), arb("0.3"))
    values = (*main.values(), *mirror.values())
    assert all(component.is_finite()
               for value in values for component in value.derivatives())
    assert any(value.d != 0 for value in (*main.values(), *mirror.values()))
