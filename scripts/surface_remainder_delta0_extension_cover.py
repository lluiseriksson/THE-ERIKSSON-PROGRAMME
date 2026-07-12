"""Design cover of the enlarged regular K2 lane ``[0,1/250]``.

The grid ladder is fixed before the exhaustive output is observed.  This file
does not emit the word CERTIFIED; promotion requires a provenance driver,
manifest, immutable transcript, and executable coverage validator.
"""

from fractions import Fraction
from time import perf_counter

from flint import ctx

import surface_remainder_delta0_extension_probe as probe


DELTA_MAX = Fraction(1, 250)
GRIDS = (96, 192, 384, 768, 1024)


def cover():
    ctx.prec = 140
    started = perf_counter()
    boxes = list(probe.sealed.born_t_boxes())
    counts = {grid: 0 for grid in GRIDS}
    worst = None
    for index, (lo, hi) in enumerate(boxes):
        for grid in GRIDS:
            c3, value, margin = probe.judge(
                DELTA_MAX, lo, hi, grid, parallel=True)
            print("TRY index", index, "t", float(lo), float(hi),
                  "grid", grid, "margin", margin, flush=True)
            if margin > 0:
                counts[grid] += 1
                lower = margin.lower()
                if worst is None or lower < worst[0]:
                    worst = (lower, index, lo, hi, grid, c3, value)
                print("ROW PASS index", index, "t", float(lo), float(hi),
                      "grid", grid, "Y3", c3, "C_value", value,
                      "margin", margin, flush=True)
                break
        else:
            print("DESIGN COVER FAIL index", index, "t", float(lo),
                  float(hi), flush=True)
            return 1
    print("DESIGN COVER PASS delta [0,0.004] boxes", len(boxes),
          "grid_counts", counts, "worst", worst,
          "elapsed_seconds", perf_counter()-started, flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(cover())
