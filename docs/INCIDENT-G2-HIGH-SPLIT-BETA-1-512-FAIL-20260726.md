# Incident — G2 high-split beta width `1/512` still fails

Date: 2026-07-26  
Scope: diagnostic only; no G2/G6 promotion.

The current paired candidate union ends at `beta=3409/32`; the residual begins
at `[3409/32,1000/9]`.  A local point probe suggested that the failed first
box `[3409/32,6819/64]` might close after beta subdivision to width `1/512`.
The first such box was run under the frozen high-split contract:

```text
beta = [3409/32,54545/512]
CWIN = 3/2; beta order = 30; t order = 37
Arb = 180 bit; MIN_DT = 1/100000
```

The production wrapper ran for 590 seconds and failed before emitting a
terminal transcript:

```text
RuntimeError: bulk failure near t=3.0615057356714304
```

The complete traceback is retained in
`scripts/surface_scaled_bulk_gap106p53125_106p533203125_split.failed.txt`.

This is a failure of the registered enclosure architecture, not a sign
disproof.  It shows that the local `1/512` width probe does not extrapolate to
an exhaustive beta/t cover.  The residual gap and `G2=BLOCKED` state remain
unchanged; no failed transcript is admitted to the candidate union.

