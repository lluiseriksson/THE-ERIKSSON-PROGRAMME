from scripts.verify_surface_high_beta_rest_perturbation_bound import verify


def test_high_beta_rest_perturbation_bound() -> None:
    result = verify()
    assert result["upper"] < 1 / 100_000
