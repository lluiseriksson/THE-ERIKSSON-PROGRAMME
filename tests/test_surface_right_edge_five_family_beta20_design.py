import pytest
from flint import arb, ctx

import surface_right_edge_five_family_beta20_design as beta20


def test_inverse_z_backend_contains_exact_bessel_values():
    ctx.prec = 160
    invz, v = arb(1)/9, arb(1)
    delta, z = invz*v, 1/invz
    i0, i1 = beta20.inverse_z_reduced_values(invz, v)
    exact0 = (-z).exp()*z.bessel_i(0)/delta.sqrt()
    exact1 = (-z).exp()*z.bessel_i(1)/delta.sqrt()
    assert i0.contains(exact0)
    assert i1.contains(exact1)


def test_inverse_z_backend_rejects_below_z8():
    ctx.prec = 140
    with pytest.raises(ValueError, match="central-chart contract"):
        beta20.inverse_z_reduced_values(arb(126)/1000, arb(1))


def test_inverse_z_backend_tightens_at_z20():
    ctx.prec = 160
    invz, v = arb(1)/25, arb(1)
    i0, i1 = beta20.inverse_z_reduced_values(invz, v)
    z, delta = 1/invz, invz*v
    exact0 = (-z).exp()*z.bessel_i(0)/delta.sqrt()
    exact1 = (-z).exp()*z.bessel_i(1)/delta.sqrt()
    assert i0.contains(exact0) and i1.contains(exact1)
    assert arb(i0.rad()) < arb("1e-5")
    assert arb(i1.rad()) < arb("1e-5")


def test_install_propagates_local_delta_ceiling():
    ctx.prec = 160
    beta20.install(arb(1)/60)
    assert beta20.ACTIVE_INVZ_CEILING < arb(1)/20
    assert beta20.ACTIVE_VALUE_FLOOR > arb(4)/5
    # Restore the default contract for tests importing this module later.
    beta20.install()


def test_symmetric_q_sum_covers_both_halves():
    ctx.prec = 140
    value = beta20.symmetric_q_sum(lambda q: q**2, arb(1), 20)
    assert value.contains(arb(2)/3)
