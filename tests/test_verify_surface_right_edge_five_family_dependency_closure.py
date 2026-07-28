import verify_surface_right_edge_five_family_dependency_closure as closure


def test_dependency_ledger_is_exact_transitive_closure():
    reached = closure.verify()
    assert "surface_remainder_carrier_jet" in reached
