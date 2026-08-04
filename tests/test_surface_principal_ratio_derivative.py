from scripts.verify_surface_principal_ratio_derivative import identities


def test_principal_ratio_derivative_identities() -> None:
    result = identities()
    assert result["dF_dC"] != 0
    assert result["bessel_score_factor"] != 0
