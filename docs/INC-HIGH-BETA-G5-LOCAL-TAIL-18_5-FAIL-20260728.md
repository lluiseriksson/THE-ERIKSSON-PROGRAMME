# Incident: local-exponential G5 cover still fails

**Observed:** 2026-07-28

**Affected design:** `SURFACE-HIGH-BETA-G5-LOCAL-TAIL-18_5-PREREG-20260728.md`

## Result

The frozen driver used the cell-local factor `exp(lambda_hi)` and was
tested at the left, middle, and right of its range.  The first cells of the
middle and right units failed after the sole permitted mixed refinement:

```text
lambda=[2.8,2.82], delta=[0,0.001]:
P0_lower=-0.0011235254..., H_lower=-0.03814684...

lambda=[3.4,3.42], delta=[0,0.001]:
P0_lower=-0.0074855206..., H_lower=-0.16170237...
```

`B0` remained positive.  The left unit emitted six positive coarse rows at
`lambda=[2,2.02]` before it was deliberately stopped.  None of the partial
rows carries theorem load.

## Diagnosis

Localizing the exponential was rigorous and did reduce all five near-tail
charges, but it did not reduce them enough once the saddle separation
grows.  The next design question is therefore geometric: enlarge the
central `q` window while preserving the moving-chart containment and the
low-argument Bessel companion.  This reduces the Gaussian near-tail charge
at its source instead of weakening a terminal sign threshold.

The failed transcripts remain in the local audit archive and are excluded
from every production union.
