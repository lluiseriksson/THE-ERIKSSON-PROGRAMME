# Scaled-bulk rescue subcell preregistration: `[101.8125,101.828125]`

**Registered:** 2026-07-21, after the parent rescue timeout and before this
subcell is run

This is a fixed first descendant of the timed-out parent
`[101.8125,102.0625]`; it is not an adaptive permission to keep bisecting.
The contract is unchanged: `CWIN=3/2`, beta order 40, t order 45, 220 Arb
bits, and `min_dt=1/200000`.  The exact beta endpoints are
`3258/32` and `1629/16`.

A green result is candidate evidence only and requires production/replay
byte identity plus the rescue validator.  Failure or timeout is retained as
an incident and leaves G2/G6 unchanged.
