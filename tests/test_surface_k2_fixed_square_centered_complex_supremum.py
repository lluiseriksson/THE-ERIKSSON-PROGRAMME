from __future__ import annotations

import sys
from pathlib import Path

from flint import acb, arb, ctx


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))

import probe_surface_k2_fixed_square_centered_complex_supremum as probe  # noqa: E402


def test_shift_centered_covariance_is_exact() -> None:
    ctx.prec = 180
    cells = [
        (arb(1), acb(2), acb(3), acb(5)),
        (arb(1), acb(7), acb(11), acb(13)),
    ]
    mass, _, _, centered = probe.assemble_centered(cells)
    direct_mass = sum((area*w for area, w, _, _ in cells), acb(0))
    wa = sum((area*w*a for area, w, a, _ in cells), acb(0))
    wg = sum((area*w*g for area, w, _, g in cells), acb(0))
    wag = sum((area*w*a*g for area, w, a, g in cells), acb(0))
    direct = 4*(wag/direct_mass-(wa/direct_mass)*(wg/direct_mass))
    assert mass.overlaps(direct_mass)
    assert centered.overlaps(direct)


def test_centered_complex_contract_is_fixed() -> None:
    assert probe.LADDER == ((24, 32), (48, 64), (96, 128))
