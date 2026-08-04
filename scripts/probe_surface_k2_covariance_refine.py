"""Refinement-only wrapper for the nominal covariance mass prerequisite."""

from flint import ctx

import probe_surface_k2_covariance_certificate as base


def main():
    ctx.prec = base.ARB_BITS
    for grid in (48, 96):
        M, Sa, Sb, between, within, bound = base.run(grid)
        print("COVARIANCE REFINE GRID", grid, "M", M,
              "M_lower", M.lower(), "between", between,
              "within", within, "finite", M.is_finite(),
              "positive", bool(M > 0), flush=True)
    print("COVARIANCE MASS REFINE ONLY; NO K2 PROMOTION", flush=True)


if __name__ == "__main__":
    main()
