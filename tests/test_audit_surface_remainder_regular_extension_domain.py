from fractions import Fraction

import audit_surface_remainder_regular_extension_domain as audit


def test_unparameterized_regular_extensions_are_quarantined():
    assert audit.affected_ranges() == {
        "regular004": Fraction(1, 250),
        "regular005": Fraction(1, 200),
    }
