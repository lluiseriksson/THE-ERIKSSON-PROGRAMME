from flint import arb, ctx
import importlib.util
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
SPEC = importlib.util.spec_from_file_location(
    "surface_remainder_positive_kd_lower",
    ROOT / "scripts" / "surface_remainder_positive_kd_lower.py",
)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)
positive_kd_lower = MODULE.positive_kd_lower


def test_kd_lower_stress_box_is_strictly_positive():
    ctx.prec = 100
    value, cells = positive_kd_lower(
        arb("0.010 +/- 0.0005"), arb("1.01 +/- 0.01"), grid=32
    )
    assert cells == 32 * 32
    assert value > 0


def test_kd_lower_reflected_saddle_uses_positive_factor_product():
    """The wide phase ball near t=pi must not erase KD positivity."""
    ctx.prec = 100
    value, cells = positive_kd_lower(
        arb("0.010 +/- 0.0005"), arb("3.09 +/- 0.01"), grid=32
    )
    assert cells == 32 * 32
    assert value > 0


def test_kd_lower_refuses_outside_companion_domain():
    ctx.prec = 80
    try:
        positive_kd_lower(arb("0.2 +/- 0.05"), arb("1 +/- 0.01"), grid=8)
    except ValueError as error:
        assert "z>=20" in str(error)
    else:
        raise AssertionError("the certified companion domain must be enforced")
