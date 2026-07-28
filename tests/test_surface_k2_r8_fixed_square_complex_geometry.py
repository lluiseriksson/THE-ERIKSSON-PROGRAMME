from pathlib import Path
import sys

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))

import certify_surface_k2_r8_fixed_square_complex_geometry as cert  # noqa: E402


def test_registered_geometry_margins():
    ctx.prec = 180
    values = cert.bounds()
    assert cert.RHO.overlaps(arb(17)/2000)
    assert cert.COMPANION_ORDER == 8
    assert values["radicand_deviation"] < arb("0.92")
    assert values["root_floor"] > arb("0.30")
    assert values["a_floor"] > arb("0.995")
    assert values["b_floor"] > arb("0.98")
