import importlib.util
from pathlib import Path
import sys

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))
SPEC = importlib.util.spec_from_file_location(
    "spatial_jet3", ROOT/"scripts"/"surface_remainder_spatial_jet3.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_exp_of_affine_has_exact_normalized_coefficients():
    ctx.prec = 140
    x, y = MOD.variable_x(arb("0.2")), MOD.variable_y(arb("-0.1"))
    value = MOD.jexp(MOD.jadd(x, y))
    e = arb("0.1").exp()
    for i, j in MOD.INDICES:
        expected = e/arb(MOD.factorial(i)*MOD.factorial(j))
        assert (value.get(i, j)-expected).contains(0)


def test_inverse_sqrt_product_identity_through_degree_three():
    ctx.prec = 140
    x = MOD.variable_x(arb("0.2"))
    root = MOD.jsqrt(MOD.jadd(1, x))
    product = MOD.jmul(root, root)
    target = MOD.jadd(1, x)
    for index in MOD.INDICES:
        assert (product.get(*index)-target.get(*index)).contains(0)
    inverse = MOD.jmul(MOD.jinv(MOD.jadd(2, x)), MOD.jadd(2, x))
    for index in MOD.INDICES:
        expected = arb(1) if index == (0, 0) else arb(0)
        assert (inverse.get(*index)-expected).contains(0)
