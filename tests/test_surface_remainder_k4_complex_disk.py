import surface_remainder_k4_complex_disk as disk


def test_disk_strictly_contains_the_physical_delta_interval():
    assert disk.RHO > disk.DELTA_MAX


def test_both_saddles_keep_the_square_root_away_from_its_branch_point():
    rows = disk.certify()
    assert set(rows) == {"main", "mirror"}
    for row in rows.values():
        assert row["delta_A_abs_upper"] < 1
        assert row["eta_lower"] > 0
        assert row["P_abs_upper"] > 0
