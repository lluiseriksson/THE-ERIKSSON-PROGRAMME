import surface_remainder_k4_real_coercivity as coercivity


def test_both_saddles_have_strict_real_coercivity_and_gap():
    rows = coercivity.certify()
    assert set(rows) == {"main", "mirror"}
    for row in rows.values():
        assert row["amplitude_squared_lower"] > 0
        assert row["p_plus_q_upper"] < 1
        assert row["gamma_lower"] > 0
        assert row["one_minus_w_lower"] > 0
        assert row["A_over_r2_lower"] > 0


def test_registered_ball_stays_inside_elementary_sine_range():
    angle = coercivity.DELTA_MAX.sqrt()*coercivity.RADIUS/2
    assert angle < coercivity.arb.pi()/2
