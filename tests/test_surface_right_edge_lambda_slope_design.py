from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = (ROOT / "scripts" /
          "surface_right_edge_lambda_slope_design.py").read_text(
              encoding="utf-8")


def test_lambda_slope_module_is_explicitly_design_only():
    assert "Design-only lambda-slope enclosure" in SOURCE
    assert "PRODUCTION" not in SOURCE


def test_all_five_pinned_variables_are_present():
    for marker in ("derivative == 1", "derivative == 3", "derivative >= 5",
                   "derivative == 2", "def _b_flat"):
        assert marker in SOURCE
    assert "family_slopes" in SOURCE
    assert "assemble_p0_slope" in SOURCE
