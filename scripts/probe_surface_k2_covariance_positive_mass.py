"""Covariance probe with pointwise-positive cell mass enclosure."""

import probe_surface_k2_covariance_certificate as base
from flint import arb


_ORIGINAL_CELL_INTEGRAL = base.cell_integral


def positive_mass_cell_integral(center, box, name, rx, ry, area):
    if name == "weight":
        # Pointwise interval enclosure of the strictly positive weight.
        value = base.coeff(box[name].v)
        return area*value
    return _ORIGINAL_CELL_INTEGRAL(center, box, name, rx, ry, area)


def main():
    base.cell_integral = positive_mass_cell_integral
    base.ctx.prec = base.ARB_BITS
    for grid in base.GRID_LIST:
        M, Sa, Sb, between, within, bound = base.run(grid)
        print("POSITIVE MASS GRID", grid, "M", M,
              "M_lower", M.lower(), "between", between,
              "within", within, "finite", M.is_finite(),
              "positive", bool(M > 0), "bound", bound, flush=True)
    print("POSITIVE MASS COVARIANCE DESIGN ONLY; NO K2 PROMOTION", flush=True)


if __name__ == "__main__":
    main()
