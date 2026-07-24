# Preregistration: CWIN=3/2 high-order rescue at 300 Arb bits

**Date:** 2026-07-24
**Scope:** candidate finite-beta scaled-bulk sign lane only. This does not
promote G2, `(H_tail)`, K2, K4, or G6.

The failed 180-bit order-30/37 unit at
`[3259/32,3261/32]` became indeterminate near `t=3.125678`. This preregisters
one changed enclosure route before any transcript is accepted:

* beta domain `[3259/32,3261/32]`;
* `CWIN=3/2`, beta Taylor order `40`, t Taylor order `50`;
* `PREC=300` Arb bits and `MIN_DT=1/100000`;
* t domain `[3/5, PI_UP-(3/2)/(3261/32)]`;
* strict acceptance `arb(upper).upper() < 0` for every adaptive t row;
* paired production/replay transcripts with byte-identical rows;
* dependencies and the exact driver hash recorded in both transcripts.

The only admissible result is a complete adjacent partition of the registered
t domain. A timeout, a non-strict upper bound, or a partial partition remains
an uncovered candidate gap.

This route is intentionally separate from the frozen 180-bit production
driver; no existing terminal manifest is rewritten by this experiment.
