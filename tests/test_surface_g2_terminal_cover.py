from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import audit_surface_g2_terminal_cover as terminal


def test_surface_g2_domain_geometry() -> None:
    result = terminal.audit_domain_geometry()
    assert result["lambda_lanes"][-1][1] == 3
    assert result["k2_cut_margin"] > 0
    assert result["joint_p_floor_upper"] <= terminal._aq(result["p_seam"])
    assert terminal.lambda3_joint.cert.LAMBDA0 == terminal.LAMBDA_THREE


def test_surface_g2_terminal_domain_cover() -> None:
    result = terminal.audit()
    assert result["promotion"] == "G2_TERMINAL_COVER_PROVED"
    assert result["seams"]["lambda"] == ["3/2", "2", "3"]
