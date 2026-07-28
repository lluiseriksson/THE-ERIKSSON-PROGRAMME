from scripts.certify_surface_high_beta_lambda4_interior import certify


def test_high_beta_lambda4_interior() -> None:
    result = certify()
    assert result["rho"] < 1 / 100
    assert result["adverse"] < 3 / 4
    assert result["relay_margin"] > 0
