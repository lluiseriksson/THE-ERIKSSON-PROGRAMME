# Scaled-bulk candidate: preregistration for `[36,37]`

Registered 2026-07-16 before the order-(13) probe.  This is a partial
candidate and cannot discharge the scaled-bulk slot.

Frozen configuration:

* `CWIN=4`, beta Taylor order 12, (t)-Taylor order 13, Arb precision 180;
* beta width `1/8`;
* eight adjacent beta boxes covering `[36,37]`;
* the same scaled Bessel derivative-tail factor as the `[35,36]` candidate;
* production/replay compare the printed beta-box records exactly.

The increased (t)-order is frozen before observing the exhaustive result.
It changes only the Taylor truncation order and its corresponding audited
derivative arrays; it does not change the sign target or the beta partition.
Even a green union loads only `[36,37]`, pending the independent sign and
global relay audit.

Production plus replay now pass from the same worktree head.  The validator
confirms eight adjacent beta boxes and 1,258 adaptive `t`-boxes with exact
semantic-record equality.  This is a reproducible partial candidate only; it
does not remove the scaled-bulk slot or close the remaining beta interval.
