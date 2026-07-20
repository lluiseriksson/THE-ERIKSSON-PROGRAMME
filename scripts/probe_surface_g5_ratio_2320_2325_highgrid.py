"""Isolated high-grid seam probe for the right-edge ratio judge."""

from __future__ import annotations

import json
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx

import surface_right_edge_five_family_beta20_design as beta20
import surface_right_edge_five_family_central_design as central
import surface_right_edge_five_family_finite_cover_design as cover
import surface_right_edge_five_family_finite_tail_design as tail
from surface_remainder_arb_jet2 import hull
from surface_right_edge_five_family_ratio_design import assemble_ratio


BOX = (Fraction(2320, 1000), Fraction(2325, 1000))


def aq(value: Fraction) -> arb:
    return arb(value.numerator) / value.denominator


def row(delta_index: int) -> dict:
    ctx.prec = 200
    delta_lo, delta_hi = cover.DELTA_BANDS[delta_index]
    beta20.install(aq(delta_hi))
    delta = hull(aq(delta_lo), aq(delta_hi))
    lam = hull(aq(BOX[0]), aq(BOX[1]))
    values = central.central_families(
        delta,
        lam,
        side=arb(5) / 2,
        qgrid=160,
        rgrid=32,
        thetagrid=8,
        phigrid=8,
    )
    charged = tuple(
        value + budget * arb("0 +/- 1")
        for value, budget in zip(values, tail.budgets(aq(delta_hi)))
    )
    q, b0 = assemble_ratio(delta, lam, charged)
    return {
        "delta_index": delta_index,
        "delta_lo": str(delta_lo),
        "delta_hi": str(delta_hi),
        "lambda_lo": str(BOX[0]),
        "lambda_hi": str(BOX[1]),
        "Q_lower": str(q.lower()),
        "B0_lower": str(b0.lower()),
        "pass": bool(q.lower() > 0 and b0.lower() > 0),
    }


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    output = root / "scripts" / "probe_surface_g5_ratio_2320_2325_highgrid.json"
    with ProcessPoolExecutor(max_workers=5) as pool:
        rows = list(pool.map(row, range(len(cover.DELTA_BANDS))))
    payload = {
        "kind": "surface-right-edge-ratio-highgrid-diagnostic",
        "arb_bits": 200,
        "qgrid": 160,
        "rgrid": 32,
        "thetagrid": 8,
        "phigrid": 8,
        "rows": rows,
        "scope": "isolated design-only diagnostic; no G5/G2/G6 promotion",
    }
    output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print("HIGHGRID RATIO DIAGNOSTIC rows", len(rows), "passes", sum(r["pass"] for r in rows))
    for result in rows:
        print(result)


if __name__ == "__main__":
    main()
