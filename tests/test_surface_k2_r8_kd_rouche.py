from pathlib import Path
import sys

from flint import acb, arb, ctx


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))

import certify_surface_k2_r8_kd_rouche as cert  # noqa: E402


def test_kd_integrand_is_finite_at_zero():
    ctx.prec = 180
    value = cert.kd_integrand(acb(0), arb("0.25"), arb("0.5"))
    assert value.is_finite()


def test_rouche_contract_is_frozen():
    assert cert.COMPANION_ORDER == 8
    assert cert.LADDER == ((24, 32), (48, 64), (96, 128))
