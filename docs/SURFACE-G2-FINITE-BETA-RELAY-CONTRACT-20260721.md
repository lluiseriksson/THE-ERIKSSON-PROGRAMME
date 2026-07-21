# Finite-beta sign/relay contract (pre-registration, 2026-07-21)

## Purpose and status

This document fixes the admissibility audit for the scaled-bulk archive before
any result from that audit is read. It is an audit contract only:
`DESIGN_ONLY`, no G2 or G6 promotion, and no manuscript slot may be removed.

The target finite-beta lane is the exact union

```text
beta in [20, 1000/9]
t    in [3/5, pi - (3/2)/beta].
```

The left splice at `19/100` belongs to the separately registered low/ordinary
bridge; the scaled-bulk audit starts at the fixed bulk seam `t=3/5` and must
overlap that bridge. The right endpoint is the moving G5 seam.

## What the audit may certify

For each manifested production/replay unit it checks, without changing any
file:

1. the manifest is current, has a production output and a replay output, and
   their recorded SHA-256 (LF-normalized SHA where supplied) agrees;
2. the transcript declares `CWIN=3/2`, a rational beta box, and a contiguous
   `trow` partition;
3. every row's outward-rounded `upper` is strictly negative, and the rows are
   adjacent with no gap or overlap;
4. the row partition covers the required closed bulk interval from `3/5` to
   `pi-(3/2)/beta_lo`, where the latter is the conservative endpoint for the
   beta box; and
5. the accepted beta boxes form an exact rational adjacency report.

The executable read-only audit is
`scripts/audit_surface_g2_relay_admissibility.py`. It emits a JSON summary to
stdout and never writes or edits a manifest.

## Non-implication that remains open

The identity

```text
W^J = exp(-8 beta) W,   W = 4 F_B^2 E'
```

does imply `upper(W^J)<0 => E'<0` after exhaustive coverage and the
independent `F_B>0` theorem. It does **not** imply the extraction hypothesis
`(H_tail)`: a common positive rescaling preserves the sign of `W` while
changing derivative majorants. Therefore this contract deliberately reports
`RELAY_LEMMA_UNPROVED` even if every archived row passes. A separate analytic
lemma must relate the normalized sign quantity to the weighted `(H_tail)`
bound, with all positive factors and the tail remainder proved before G2 can
change state.

The audit's exact failure report is part of the evidence: missing beta cells,
non-admissible CWIN, t-seam deficiencies, stale/missing outputs, and the
unproved relay lemma are listed separately. No relabelling or endpoint move is
permitted in response to a failure.
