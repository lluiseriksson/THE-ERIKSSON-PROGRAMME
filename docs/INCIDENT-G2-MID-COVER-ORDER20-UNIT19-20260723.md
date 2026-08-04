# G2 mid-cover order-20 timeout — unit 19

The current-tree order-20 regeneration of the `[193/4,69]` mid cover
completed units 10–18 and 30–31, then reached unit 19
`[53,213/4]` and exhausted the 600-second operational ceiling while
searching the moving `t` edge.  No fresh transcript for units 19 or 20 was
emitted in that concurrent run.  A later isolated rerun with no competing
processes completed unit 19 (152 rows); unit 20 remained beyond the same
operational ceiling.  The historical file for unit 20 retains earlier
provenance and is not admissible for the current run.

This is an operational/conditioning failure of the frozen order-20 evaluator
at unit 20, not a sign counterexample.  The cover remains incomplete and
quarantined.  The order-22 repair for unit 20 was subsequently preregistered
and is reported separately in
`SURFACE-G2-MID-COVER-ORDER22-REPAIR-UNIT20-RESULT-20260724.md`.
It resolves the operational timeout for that unit but remains quarantined
sign evidence; no G2/G6 state changes follow from the repair.
