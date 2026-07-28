import sys
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import certify_surface_high_beta_g5_ratio_side4_lambda3 as cert


def test_frozen_ratio_side4_partition() -> None:
    assert cert.UNITS == tuple(
        (start, start + 5) for start in range(100, 150, 5)
    )
    cert.ctx.prec = 140
    cert.verify_geometry()


def test_ratio_judge_is_exactly_p0_over_b0() -> None:
    a0, a1, b0, b1, lam = sp.symbols(
        "A0 A1 B0 B1 lambda", nonzero=True
    )
    p0 = a0 * b0 + lam**2 * (a1 * b0 - a0 * b1) / 4
    ratio = a0 * (1 - lam**2 * b1 / (4 * b0)) + lam**2 * a1 / 4
    assert sp.cancel(p0 - b0 * ratio) == 0
