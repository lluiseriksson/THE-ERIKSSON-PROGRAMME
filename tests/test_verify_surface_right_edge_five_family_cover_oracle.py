import verify_surface_right_edge_five_family_cover_oracle as oracle


def test_cover_row63_contains_fourier_oracle():
    assert oracle.verify() > 0
