import importlib.util
from pathlib import Path
import sys

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))
SPEC = importlib.util.spec_from_file_location(
    "delta0_core",
    ROOT/"scripts"/"surface_remainder_delta0_core_integrator.py",
)
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_regular_delta0_core_integral_is_finite():
    ctx.prec = 120
    delta = MOD.hull(arb(0), arb(1)/100)
    values = MOD.integrate_core(delta, arb("2.9"), 4)
    assert set(values) == set(MOD.NAMES)
    assert all(value.is_finite() for value in values.values())
