from fractions import Fraction

import surface_remainder_k4_transport as transport


def test_physical_second_derivative_requires_all_transport_terms():
    for a in range(6):
        for b in range(7):
            for c in range(7):
                assert transport.transported_second_coefficient(a, b, c) == (
                    transport.physical_second_coefficient(a, b, c))


def test_naive_scaled_second_derivative_is_not_the_physical_one():
    # g=sigma^2 is independent of delta at fixed scaled coordinates, while
    # f=s^2/delta has a nonzero second derivative at fixed physical s.
    assert transport.physical_second_coefficient(0, 2, 0) == Fraction(2)
    assert Fraction(0) != transport.physical_second_coefficient(0, 2, 0)


def test_integrated_mass_identity_is_exact():
    for a in range(8):
        direct, chart = transport.integrated_mass_second_coefficients(a)
        assert direct == chart
