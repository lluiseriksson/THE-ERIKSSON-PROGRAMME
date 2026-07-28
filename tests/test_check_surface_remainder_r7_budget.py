import importlib.util
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))
SPEC = importlib.util.spec_from_file_location(
    "check_r7", ROOT/"scripts"/"check_surface_remainder_r7_budget.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_registered_r7_budget_has_strict_slack():
    assert MOD.check(2000) > 150000
