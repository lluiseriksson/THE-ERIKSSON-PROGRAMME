import importlib.util
from pathlib import Path
import sys

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))
SPEC = importlib.util.spec_from_file_location(
    "delta0_fourth",
    ROOT/"scripts"/"surface_remainder_delta0_fourth_coefficient.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_target_fourth_coefficient_is_regular_on_c_window():
    c = sp.symbols("c", positive=True)
    value = sp.factor(MOD.target_y3(c))
    assert value.subs(c, 1) == sp.Rational(-39, 1024)
    assert value.subs(c, sp.sqrt(2)/2) == sp.Rational(551, 128)
