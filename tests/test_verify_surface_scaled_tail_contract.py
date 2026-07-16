from verify_surface_scaled_tail_contract import check_box


def test_scaled_tail_contract_boxes():
    from fractions import Fraction
    for lo, hi in ((Fraction(20), Fraction(201, 10)),
                   (Fraction(40), Fraction(401, 10)),
                   (Fraction(80), Fraction(801, 10)),
                   (Fraction(111), Fraction(1000, 9))):
        rb, ra = check_box(lo, hi)
        assert rb.upper() < 1 and ra.upper() < 1
