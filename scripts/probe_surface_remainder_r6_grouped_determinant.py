"""Design-only grouped double-sum determinant enclosure for R6.

The global bilinear determinant is expanded as
  sum_{i,j} (KD_i*HDF_j - KF_i*HDD_j)
over spatial groups.  Grouping is an interval-dependency experiment; it does
not include the annulus, outer tail, companion error, or terminal judge.
"""
from fractions import Fraction

from flint import arb, arb_series, ctx

import surface_remainder_delta0_extension_probe as regular
from surface_remainder_arb_jet2 import hull

N = 7


def aq(q):
    return arb(q.numerator) / arb(q.denominator)


def group_moments(tlo, thi, grid=64, groups=8):
    if grid % groups:
        raise ValueError("grid must be divisible by groups")
    base = hull(arb(9)/1000, arb(1)/100)
    t = hull(aq(tlo), aq(thi))
    width = arb(12)/grid
    span = grid//groups
    names = ("kd", "kf", "hdd", "hdf")
    out = [{name: arb_series([arb(0)]*N, N) for name in names}
           for _ in range(groups*groups)]
    for i in range(grid):
        for j in range(grid):
            sigma = hull(width*i, width*(i+1))
            tau = hull(width*j, width*(j+1))
            values = regular.nominal_moment_series(base, t, sigma, tau, N)
            area = 4*width**2
            slot = (i//span)*groups + j//span
            for name, series in values.items():
                out[slot][name] += area*series
    return out, t


def assemble(groups, t):
    names = ("kd", "kf", "hdd", "hdf")
    totals = {name: arb_series([arb(0)]*N, N) for name in names}
    numerator = arb_series([arb(0)]*N, N)
    for left in groups:
        for name in names:
            totals[name] += left[name]
    for left in groups:
        for right in groups:
            numerator += left["kd"]*right["hdf"] \
                - left["kf"]*right["hdd"]
    coeffs = numerator.coeffs()+[arb(0)]*N
    quotient = arb_series(coeffs[1:7], 6)
    y = 4*quotient/totals["kd"]**2
    return y, numerator, totals


def run(index=0, grid=64, groups=8):
    boxes = list(regular.sealed.born_t_boxes())
    lo, hi = boxes[index]
    grouped, t = group_moments(lo, hi, grid, groups)
    y, numerator, totals = assemble(grouped, t)
    coeff = (y.coeffs()+[arb(0)]*8)[5]
    print("R6 GROUPED DETERMINANT DESIGN", "index", index,
          "grid", grid, "groups", groups)
    print("KD0", totals["kd"].coeffs()[0].str(24))
    print("B0", numerator.coeffs()[0].str(24))
    print("Y5", coeff.str(30))
    print("Y5_RADIUS", coeff.rad().str(24))
    print("SCOPE diagnostic only; no K2/H_tail/G2/G6 promotion")


if __name__ == "__main__":
    ctx.prec = 100
    run()
