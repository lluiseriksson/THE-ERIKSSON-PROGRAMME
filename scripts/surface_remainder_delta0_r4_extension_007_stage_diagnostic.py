"""Pre-registered stage diagnostic for the unresolved delta<=0.007 probe.

This file does not judge positivity and is not certificate evidence.  It
isolates the first operation whose interval contract is unresolved on the
already registered adversarial t-box, without changing any production input.
"""

from flint import ctx

import surface_remainder_delta0_extension_probe as regular
import surface_remainder_delta0_outer_domain_v4 as outer
import surface_remainder_delta0_r4_extension_007_probe as probe


def main():
    ctx.prec = 140
    lo, hi = list(regular.sealed.born_t_boxes())[-1]
    t = regular.hull(regular.aq(lo), regular.aq(hi))
    print("R4 007 STAGE DIAGNOSTIC", "t", lo, hi, flush=True)

    for grid in probe.GRIDS:
        print("GRID", grid, flush=True)
        cores = []
        for index, (dlo, dhi) in enumerate(probe.CORE_BOXES):
            try:
                lane = regular.hull(regular.aq(dlo), regular.aq(dhi))
                core = regular.parallel_integrate_coefficients(lane, t, grid)
            except (ValueError, ZeroDivisionError) as exc:
                print("FAIL CORE", index, dlo, dhi, type(exc).__name__,
                      str(exc), flush=True)
                break
            cores.append(core)
            print("PASS CORE", index, dlo, dhi, flush=True)
        else:
            for index, (dlo, dhi) in enumerate(probe.ANNULUS_BOXES):
                if dhi <= probe.CORE_BOXES[0][1]:
                    source = cores[0]
                elif dhi <= probe.CORE_BOXES[1][1]:
                    source = cores[1]
                else:
                    source = cores[2]
                try:
                    bounds = outer.outer_derivative_bounds_box_to(
                        dlo, dhi, probe.PHYSICAL_INNER)
                    outer.add_outer_derivatives_box_to(
                        source, dlo, dhi, probe.PHYSICAL_INNER)
                except (ValueError, ZeroDivisionError) as exc:
                    print("FAIL ANNULUS", index, dlo, dhi,
                          type(exc).__name__, str(exc), flush=True)
                    break
                widths = tuple(len(bounds[name]) for name in sorted(bounds))
                print("PASS ANNULUS", index, dlo, dhi, widths, flush=True)
            else:
                print("PASS ALL STAGES", grid, flush=True)
                continue
        # A finer grid cannot repair a failure in an outer annulus enclosure.
        # Stop after the first such localization; core failures remain
        # grid-dependent and proceed to the next registered grid.
        if "index" in locals() and len(cores) == len(probe.CORE_BOXES):
            return 1
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
