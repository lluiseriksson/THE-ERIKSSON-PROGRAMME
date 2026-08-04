"""Design-only cellwise gauge probe for the R6 determinant.

The exact identity
  N = KD*(HDF-lambda*HDD) - (KF-lambda*KD)*HDD
is applied to each spatial-cell contribution before summation.  This is a
dependency diagnostic only: it omits the annulus, outer tail, companion
charge, and terminal weighted judge.
"""
from fractions import Fraction

from flint import arb, arb_series, ctx

import surface_remainder_delta0_extension_probe as regular
from surface_remainder_delta0_r6_extension_010_cover import assemble_y_six
from surface_remainder_arb_jet2 import hull

N = 7


def aq(q):
    return arb(q.numerator) / arb(q.denominator)


def aggregate(tlo, thi, grid):
    # The nominal series has a nonzero leading denominator; use the positive
    # tenth-birth lane.  The delta=0 endpoint requires the separate regular
    # endpoint carrier and is intentionally outside this diagnostic.
    base = hull(arb(9) / 1000, arb(1) / 100)
    t = hull(aq(tlo), aq(thi))
    width = arb(12) / grid
    raw = {name: arb_series([arb(0)] * N, N)
           for name in ("kd", "kf", "hdd", "hdf")}
    cells = []
    for i in range(grid):
        for j in range(grid):
            sigma = hull(width*i, width*(i+1))
            tau = hull(width*j, width*(j+1))
            values = regular.nominal_moment_series(base, t, sigma, tau, N)
            area = 4 * width**2
            cell = {name: area*series for name, series in values.items()}
            cells.append(cell)
            for name, series in cell.items():
                raw[name] += series
    return raw, cells, t


def midpoint(x):
    return (arb(x.lower()) + arb(x.upper())) / 2


def run(index=0, grid=64):
    boxes = list(regular.sealed.born_t_boxes())
    lo, hi = boxes[index]
    raw, cells, t = aggregate(lo, hi, grid)
    print("KD0", raw["kd"].coeffs()[0].str(30))
    kd0 = midpoint(raw["kd"].coeffs()[0])
    hdd0 = midpoint(raw["hdd"].coeffs()[0])
    lam = (midpoint(raw["hdf"].coeffs()[0]) / hdd0
           + midpoint(raw["kf"].coeffs()[0]) / kd0) / 2

    gauged = {name: arb_series([arb(0)] * N, N)
              for name in ("kd", "kf", "hdd", "hdf")}
    for cell in cells:
        gauged["kd"] += cell["kd"]
        gauged["hdd"] += cell["hdd"]
        gauged["hdf"] += cell["hdf"] - lam*cell["hdd"]
        gauged["kf"] += cell["kf"] - lam*cell["kd"]

    raw_y = assemble_y_six(raw, t)
    gauged_y = assemble_y_six(gauged, t)
    raw_c = (raw_y.coeffs() + [arb(0)]*8)[5]
    gauged_c = (gauged_y.coeffs() + [arb(0)]*8)[5]
    print("R6 CELLWISE GAUGE DESIGN", "index", index, "grid", grid)
    print("lambda", lam.str(30))
    print("RAW_Y5", raw_c.str(30))
    print("GAUGED_Y5", gauged_c.str(30))
    print("IDENTITY_DIFF", (raw_c-gauged_c).str(30))
    print("RAW_RADIUS", raw_c.rad().str(20))
    print("GAUGED_RADIUS", gauged_c.rad().str(20))
    print("SCOPE diagnostic only; no K2/H_tail/G2/G6 promotion")


if __name__ == "__main__":
    ctx.prec = 100
    run()
