import runpy


def test_scaled_tail_oracle(capsys):
    runpy.run_module("surface_finite_beta_scaled_tail_oracle", run_name="__main__")
    assert "SCALED FOURIER TAIL ORACLE PASS; FINITE-SUM CHECK ONLY" in capsys.readouterr().out
