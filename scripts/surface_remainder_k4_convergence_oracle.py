"""Local K4 convergence oracle for the registered positive endpoint box.

The same fixed delta interval is evaluated on the deterministic 576-cell and
1152-cell spatial ladders.  Every literal S1''' fraction must contract and
the refined level must be strictly subunit.  This closes only a local
convergence gate; it does not create a delta union or a K4 theorem claim.
"""

from flint import arb, ctx

import surface_remainder_centered_delta_integrator_design as design


def main():
    ctx.prec = 140
    lo, hi = arb("0.049"), arb("0.05")
    levels = {}
    for cells in (576, 1152):
        totals, count, fallbacks = design.adaptive_integral(
            lo, hi, max_cells=cells)
        assert count == cells and all(v.is_finite() for v in totals.values())
        levels[cells] = design.single_box_fractions(totals, lo, hi)
        print("LEVEL", cells, "fallbacks", fallbacks,
              {name: value.str(14) for name, value in levels[cells].items()},
              flush=True)
    names = tuple(design.BUDGETS)
    for name in names:
        coarse, fine = levels[576][name], levels[1152][name]
        if not (fine < coarse and fine < 1):
            raise SystemExit(("non-contracting K4 endpoint fraction", name,
                              coarse, fine))
    print("K4 CONVERGENCE ORACLE PASS; LOCAL ENDPOINT ONLY")


if __name__ == "__main__":
    main()
