from scripts.audit_surface_k4_global_judge import audit


def test_historical_k4_rows_do_not_pass_the_global_judge():
    result = audit()
    assert result["positive_band_count"] == 39
    assert result["positive_delta_union"] == ["61/2000", "1/20"]
    assert result["high_beta_delta_max"] == "9/1000"
    assert set(result["failed_global_rows"]) == {
        "MD2r_mirror", "muF_main", "nuD_main", "nuF_main"
    }
    assert result["historical_failed_rows"]
