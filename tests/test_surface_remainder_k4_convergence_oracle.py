import runpy


def test_k4_convergence_oracle(capsys):
    runpy.run_module("surface_remainder_k4_convergence_oracle", run_name="__main__")
    assert "K4 CONVERGENCE ORACLE PASS; LOCAL ENDPOINT ONLY" in capsys.readouterr().out
