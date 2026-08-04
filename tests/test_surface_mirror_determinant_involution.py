from scripts.verify_surface_mirror_determinant_involution import verify


def test_mirror_determinant_involution():
    result = verify()
    assert result["adverse_mirror"] == result["weighted_transformed_X"]
