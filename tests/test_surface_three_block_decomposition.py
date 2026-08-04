from scripts.verify_surface_three_block_decomposition import identities


def test_three_block_decomposition() -> None:
    result = identities()
    assert set(result) == {
        "x1",
        "xfull",
        "assembled",
        "rest_adverse",
        "rest_adverse_expanded",
    }
