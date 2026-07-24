# K4 lower-band probe timeout (2026-07-24)

The isolated centred-delta probe for the prospective band
`delta=[0.026,0.0275]`, `t=2.9`, seed grid 12 and maximum 16,384 cells was
run against the current carrier branch with 140-bit Arb.  It did not produce
a transcript before the 120-second execution limit and emitted no terminal
verdict.

This is an execution/design failure, not a numerical pass or disproof.  No
file from the probe is admitted to any K4 union, and no K4, `S1'''/S2'''`, G2,
or G6 status changes follow from it.  A future attempt must use a fresh
pre-registration and an explicitly bounded budget; it must not silently reuse
the candidate bands above `delta=0.0275`.
