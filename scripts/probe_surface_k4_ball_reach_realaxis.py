"""Finite real-axis stress probe for the K4 regular-ball alternative.

This is intentionally not a certificate: it omits the delta=0 continuation
and both spatial/phi tails.  It only checks that the fixed-scaled-coordinate
combination ``2 Dg + delta D^2 g`` can be enclosed with the existing TJet
backend on a registered positive-delta stress box.
"""

from __future__ import annotations

import hashlib
import platform
import subprocess
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx

from surface_remainder_arb_jet2 import hull
from surface_remainder_centered_delta_carrier import (
    scaled_main_carriers,
    scaled_mirror_carriers,
)
from surface_remainder_tjet import tjet

ROOT = Path(__file__).resolve().parents[1]
T = Fraction(29, 10)
DELTA_LO = Fraction(1, 100)
DELTA_HI = Fraction(1, 15)
RADIUS = Fraction(4)
GRID = 8


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    ctx.prec = 140
    head = subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}", "rev-parse", "HEAD"],
        cwd=ROOT, text=True).strip()
    delta_lo = arb(DELTA_LO.numerator) / arb(DELTA_LO.denominator)
    delta_hi = arb(DELTA_HI.numerator) / arb(DELTA_HI.denominator)
    delta_box = hull(delta_lo, delta_hi)
    t = arb(T.numerator) / arb(T.denominator)
    edges = [arb(-RADIUS.numerator) / arb(RADIUS.denominator)
             + 2*arb(RADIUS.numerator) / arb(RADIUS.denominator)*arb(i)/GRID
             for i in range(GRID + 1)]
    names = (
        "muF_main", "nuD_main", "nuF_main",
        "MD_mirror", "MF_mirror", "MD2r_mirror", "MDFr_mirror",
    )
    totals = {name: arb(0) for name in names}
    domain_gap = None
    for i in range(GRID):
        for j in range(GRID):
            sigma = hull(edges[i], edges[i + 1])
            tau = hull(edges[j], edges[j + 1])
            delta = tjet(delta_box, 1)
            try:
                values = scaled_main_carriers(delta, t, sigma, tau)
                values.update(scaled_mirror_carriers(delta, t, sigma, tau))
            except ValueError as exc:
                domain_gap = (i, j, str(exc))
                break
            area = (edges[i + 1] - edges[i]) * (edges[j + 1] - edges[j])
            for name in names:
                # D and D^2 are ordinary derivatives stored by TJet.
                totals[name] += area * (2*values[name].d
                                         + delta_box*values[name].d2)
        if domain_gap is not None:
            break
    print("K4 REALAXIS STRESS PROBE")
    print("python", platform.python_version())
    print("arb_bits", ctx.prec)
    print("git_head", head)
    print("script_sha256", sha256(Path(__file__)))
    print("config", "t", T, "delta", DELTA_LO, DELTA_HI,
          "scaled_radius", RADIUS, "grid", GRID)
    if domain_gap is not None:
        print("K4 REALAXIS DOMAIN_GAP", domain_gap)
        print("SCOPE diagnostic only; low-z partition and tails remain open")
        return 1
    for name in names:
        value = totals[name]
        print(name, "finite", value.is_finite(), "upper_abs",
              value.abs_upper().str(24))
        if not value.is_finite():
            print("K4 REALAXIS NONFINITE")
            print("SCOPE diagnostic only; no K4/G6 promotion")
            return 1
    print("K4 REALAXIS FINITE")
    print("SCOPE positive-delta stress only; delta=0 and tails open")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
