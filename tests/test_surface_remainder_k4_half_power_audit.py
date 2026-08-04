from fractions import Fraction

import surface_remainder_k4_half_power_audit as audit


def test_all_seven_integrated_masses_have_integer_zero_valuation():
    values = audit.audit()
    assert len(values) == 7
    assert set(values.values()) == {Fraction(0)}


def test_scaled_bessel_prefactors_cancel_half_powers():
    assert audit.A_SCALED == Fraction(3, 2)
    assert audit.B_SCALED == Fraction(5, 2)
    assert audit.KERNEL == -1
    assert audit.HB == 1


def test_geometric_leading_terms_supply_the_required_main_zero():
    for cc in (Fraction(-1, 3), Fraction(0), Fraction(2, 5), Fraction(1)):
        sigma2, tau2 = audit.main_f_first_coefficients(cc)
        assert sigma2 == -(2*cc+1)
        assert tau2 == 0
        assert audit.mirror_f_constant(cc) == 4*cc
