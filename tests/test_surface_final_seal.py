from scripts.audit_surface_final_seal import audit


def test_surface_final_seal() -> None:
    assert audit() == []
