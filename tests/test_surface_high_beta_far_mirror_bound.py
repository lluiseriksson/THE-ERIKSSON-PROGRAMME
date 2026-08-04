from scripts.verify_surface_high_beta_far_mirror_bound import verify


def test_high_beta_far_mirror_bound() -> None:
    result = verify()
    assert result["upper"] < 1
