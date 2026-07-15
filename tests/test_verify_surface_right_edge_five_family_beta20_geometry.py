import verify_surface_right_edge_five_family_beta20_geometry as geometry


def test_beta20_central_geometry():
    angle, value = geometry.verify()
    assert angle > 0
    assert value > 0
