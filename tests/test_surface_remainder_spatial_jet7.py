import importlib.util
from pathlib import Path

from flint import arb


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "spatial_jet7", ROOT/"scripts"/"surface_remainder_spatial_jet7.py")
MOD = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(MOD)


def test_inverse_and_sqrt_identities_through_degree_seven():
    x = MOD.variable_x(arb("0.2"))
    value = MOD.jadd(2, x)
    inverse = MOD.jmul(value, MOD.jinv(value))
    root = MOD.jsqrt(value)
    square = MOD.jmul(root, root)
    for index in MOD.INDICES:
        expected = arb(1) if index == (0, 0) else arb(0)
        assert (inverse.get(*index)-expected).contains(0)
        assert (square.get(*index)-value.get(*index)).contains(0)
