from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = (ROOT / "scripts" /
          "certify_surface_scaled_pair_taylor_cell.py").read_text(
              encoding="utf-8"
          )


def test_cell_driver_records_all_four_error_components():
    for marker in ("finite", "mode_tail", "lambda_remainder",
                   "beta_remainder", "total_upper"):
        assert marker in SOURCE


def test_cell_driver_is_not_a_global_promotion():
    assert "SCOPE one rational cell only" in SOURCE
    assert "no G2/G6 promotion" in SOURCE
