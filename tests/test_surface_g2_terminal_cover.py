from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import audit_surface_g2_weak_terminal_cover as terminal


def test_surface_g2_domain_geometry() -> None:
    result = terminal.audit_domain_geometry()
    assert result["weak_t_union"] == [0, terminal.PI_UP]
    assert result["weak_t_seam"] == terminal.Fraction(21, 10)
    assert result["joint_p_floor_upper"] <= terminal._aq(result["p_seam"])


def test_surface_g2_terminal_domain_cover() -> None:
    result = terminal.audit()
    assert result["promotion"] == "G2_WEAK_TERMINAL_COVER_PROVED"
    assert result["lambda_seams"] == ["3/2", "2", "3"]
    assert result["weak_main_lanes"] == {
        "far": ["0", "21/10"],
        "near": ["21/10", "31415927/10000000"],
    }
