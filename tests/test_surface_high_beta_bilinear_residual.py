from scripts.verify_surface_high_beta_bilinear_residual import verify


def test_two_group_bilinear_residual_identity():
    result = verify()
    assert result["full"] == result["grouped"]
