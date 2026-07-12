import importlib.util
from pathlib import Path
import sys

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))
SPEC = importlib.util.spec_from_file_location(
    "delta0_fifth",
    ROOT/"scripts"/"surface_remainder_delta0_fifth_coefficient.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_target_fifth_coefficient_endpoint_values():
    c = sp.symbols("c", positive=True)
    value = sp.factor(MOD.target_y4(c))
    assert value.subs(c, 1) == sp.Rational(-86319, 262144)
    assert sp.simplify(value.subs(c, sp.sqrt(2)/2)
                       -sp.Rational(494883, 32768)*sp.sqrt(2)) == 0
