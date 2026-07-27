from scripts.verify_surface_mirror_cross_decomposition import identities


def test_mirror_cross_decomposition() -> None:
    result = identities()
    assert set(result) == {
        "adverse",
        "cross",
        "mirror_determinant",
        "weighted_xp",
        "ratio_cross",
        "ratio_reduced",
    }
