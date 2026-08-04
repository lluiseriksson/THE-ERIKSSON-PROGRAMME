from pathlib import Path
import sys


SCRIPTS = Path(__file__).resolve().parents[1] / "scripts"
sys.path.insert(0, str(SCRIPTS))

from verify_surface_high_beta_main_positive import verify


def test_k2_main_carrier_is_positive():
    result = verify()
    assert result["passed"]
    assert result["boxes"] > 150
    assert result["worst_lower"] > 0
