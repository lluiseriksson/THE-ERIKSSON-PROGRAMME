import runpy


def test_transport_oracle_passes_at_positive_stress_point(capsys):
    runpy.run_module("surface_remainder_k4_transport_oracle", run_name="__main__")
    out = capsys.readouterr().out
    assert "K4 TRANSPORT ORACLE PASS; LOCAL IDENTITY ONLY" in out
