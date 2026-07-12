"""Design probe that groups the K2 determinant before interval summation.

This is deliberately not a certificate driver.  It reuses the rigorously
enclosed degree-five cell integrals, but combines every unordered pair before
summing.  The regrouping is an exact finite identity and can therefore reveal
whether interval dependency in the four separately accumulated moments is the
dominant loss.  A successful probe would still require a terminal driver and
all three accounting tracks.
"""

from flint import arb, ctx

import surface_remainder_positive_physical_series_design as base
import surface_remainder_positive_t_centered as engine
from surface_remainder_tjet import tjet


PREC = engine.PREC


def pairwise_numerator(cells):
    """Return the exact determinant sum, grouped by unordered cell pairs."""
    out = [tjet(0) for _ in range(PREC)]
    for i, left in enumerate(cells):
        out = engine._sadd(out, engine._sadd(
            engine._smul(left["KD"], left["HDF"]),
            engine._sneg(engine._smul(left["KF"], left["HDD"]))))
        for right in cells[i+1:]:
            cross = engine._sadd(
                engine._smul(left["KD"], right["HDF"]),
                engine._sneg(engine._smul(left["KF"], right["HDD"])))
            cross = engine._sadd(cross, engine._sadd(
                engine._smul(right["KD"], left["HDF"]),
                engine._sneg(engine._smul(right["KF"], left["HDD"]))))
            out = engine._sadd(out, cross)
    return out


def scalar_row(row):
    return [value.v for value in row]


def scalar_add(a, b):
    return [x+y for x, y in zip(a, b)]


def scalar_neg(a):
    return [-x for x in a]


def scalar_mul(a, b):
    return [sum((a[k]*b[n-k] for k in range(n+1)), arb(0))
            for n in range(PREC)]


def scalar_inv(a):
    out = [arb(0) for _ in range(PREC)]
    out[0] = 1/a[0]
    for n in range(1, PREC):
        out[n] = -out[0]*sum((a[k]*out[n-k]
                              for k in range(1, n+1)), arb(0))
    return out


def scalar_evaluate_through(row, perturbation, degree=5):
    out = arb(0)
    for value in reversed(row[:degree+1]):
        out = out*perturbation+value
    return out


def scalar_pairwise_numerator(cells):
    """Value-only counterpart used to keep the diagnostic inexpensive."""
    rows = [{name: scalar_row(row) for name, row in cell.items()}
            for cell in cells]
    out = [arb(0) for _ in range(PREC)]
    for i, left in enumerate(rows):
        out = scalar_add(out, scalar_add(
            scalar_mul(left["KD"], left["HDF"]),
            scalar_neg(scalar_mul(left["KF"], left["HDD"]))))
        for right in rows[i+1:]:
            cross = scalar_add(
                scalar_mul(left["KD"], right["HDF"]),
                scalar_neg(scalar_mul(left["KF"], right["HDD"])))
            cross = scalar_add(cross, scalar_add(
                scalar_mul(right["KD"], left["HDF"]),
                scalar_neg(scalar_mul(right["KF"], left["HDD"]))))
            out = scalar_add(out, cross)
    return out


def summed_moments(cells):
    totals = {name: [tjet(0) for _ in range(PREC)]
              for name in ("KD", "KF", "HDD", "HDF")}
    for cell in cells:
        for name, row in cell.items():
            totals[name] = engine._sadd(totals[name], row)
    return totals


def assemble_from_numerator(numerator, kd, delta):
    d = [tjet(delta), tjet(1)]+[tjet(0)]*(PREC-2)
    dinv4 = engine._sinv(engine._smul(engine._smul(
        engine._smul(d, d), d), d))
    kdinv = engine._sinv(kd)
    return [4*x for x in engine._smul(
        numerator, engine._smul(dinv4, engine._smul(kdinv, kdinv)))]


def cells(delta, t, grid=8):
    pilot = base.integrate_moments(delta, t, 24)
    ratio = pilot["KF"]/pilot["KD"]
    calibration = [arb(value.mid()) for value in ratio.coeffs()]
    calibration += [arb(0)]*(PREC-len(calibration))
    width = arb("1.2")/grid
    return [engine.centered_cell(
        delta, t, width*i, width*(i+1), width*j, width*(j+1), calibration)
        for i in range(grid) for j in range(grid)]


def main():
    ctx.prec = 120
    delta, radius, t = arb("0.0495"), arb("0.0005"), arb("1.01")
    perturbation = engine.spatial.hull(-radius, radius)
    cell_rows = cells(delta, t)
    totals = summed_moments(cell_rows)
    scalar_totals = {name: scalar_row(row) for name, row in totals.items()}
    direct_numerator = scalar_add(
        scalar_mul(scalar_totals["KD"], scalar_totals["HDF"]),
        scalar_neg(scalar_mul(scalar_totals["KF"], scalar_totals["HDD"])))
    d = [delta, arb(1)]+[arb(0)]*(PREC-2)
    factor = scalar_mul(scalar_inv(scalar_mul(
        scalar_mul(scalar_mul(d, d), d), d)),
        scalar_mul(scalar_inv(scalar_totals["KD"]),
                   scalar_inv(scalar_totals["KD"])))
    direct = [4*x for x in scalar_mul(direct_numerator, factor)]
    grouped = [4*x for x in scalar_mul(
        scalar_pairwise_numerator(cell_rows), factor)]
    head = [value.v for value in engine.exact_head(
        delta, tjet(t, 1, 0))]
    direct_residual = scalar_evaluate_through(
        scalar_add(direct, scalar_neg(head)), perturbation)
    grouped_residual = scalar_evaluate_through(
        scalar_add(grouped, scalar_neg(head)), perturbation)
    print("PAIRWISE GRID8 direct", direct_residual.abs_upper(),
          "grouped", grouped_residual.abs_upper(),
          "ratio", direct_residual.abs_upper()/grouped_residual.abs_upper())
    print("PAIRWISE PROBE DESIGN ONLY")


if __name__ == "__main__":
    main()
