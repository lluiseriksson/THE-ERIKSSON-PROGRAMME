# Incident — post-1635/16 MIN_DT=10⁻⁸ full-cell diagnostic failed

Date: 2026-07-25

## Preregistration

The campaign was preregistered in `docs/SURFACE-G2-POST1635-MIN8-CELL-PREREG-20260725.md` and run by `scripts/run_surface_g2_post1635_min8_cell.py`. It used the fixed beta cell `[1635/16,3271/32]`, the existing five t partitions, seeded step `1/64`, CWIN `3/2`, orders beta/t `30/37`, Arb precision `180`, and recursive `MIN_DT=1/100000000`.

## Result

The production run exited nonzero after approximately `435.8 s` with:

```text
RuntimeError: bulk failure near t=3.1231041252468428
```

No certification transcript was emitted. The failure is therefore an inconclusive enclosure at the hard floor, not a proof of either sign. It does not promote G2 or G6 and does not alter the authoritative coverage audit.

The replay was run with the identical command and exited after approximately `444.0 s` at the same failure location `t=3.1231041252468428`. Both stdout transcript files are empty because the driver emits a transcript only after a complete cover. Promotion remains `NONE`; the candidate remains quarantined.

## Interpretation

This is the third independent post-1635/16 failure after the seeded full cell and the width-`1/32` cell. Refining the minimum width does not close the two-dimensional box. The earlier one-row micro-rescue is local evidence only and cannot be promoted to a cell-wide theorem.

The next admissible route is analytic or a stronger interval enclosure (for example, a higher-order Taylor/derivative or convexity certificate). No manuscript slot may be removed on the basis of this incident.
