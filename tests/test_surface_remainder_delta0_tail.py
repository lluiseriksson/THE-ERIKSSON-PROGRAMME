import importlib.util
from pathlib import Path
import sys

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))
SPEC = importlib.util.spec_from_file_location(
    "delta0_tail", ROOT/"scripts"/"surface_remainder_delta0_tail.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_outer_tail_bounds_are_finite_positive_and_small():
    ctx.prec = 180
    bounds = MOD.tail_bounds()
    for value in bounds.__dict__.values():
        assert value.is_finite() and value > 0
        assert value < arb("1e-8")
