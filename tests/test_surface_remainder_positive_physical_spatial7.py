import importlib.util
from pathlib import Path
import sys

from flint import arb


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))
SPEC = importlib.util.spec_from_file_location(
    "physical7", ROOT/"scripts"/"surface_remainder_positive_physical_spatial7.py")
MOD = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(MOD)


def test_one_degree_seven_parameter_cell_is_finite():
    from surface_remainder_tjet import tjet
    values = MOD.centered_cell(
        arb("0.04975"), tjet(arb("2.9"), 1),
        arb(0), arb("0.03"), arb(0), arb("0.03"),
        [arb(0)]*MOD.PREC)
    assert all(value.v.is_finite() and value.d4.is_finite()
               for row in values.values() for value in row)
