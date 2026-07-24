"""Regression for the interval-safe Bessel-series stopping criterion."""

from mpmath import iv

import certify_thmB


def test_high_order_enclosure_terminates_without_float_underflow():
    iv.prec = 80
    value = certify_thmB.enc_I_at(87, 60001, 1_000_000)
    assert value.a > 0
    assert value.b < iv.mpf("1e-260")
