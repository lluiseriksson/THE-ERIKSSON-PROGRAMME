# Incident: G2 pair mean-value cell fails at the 1/32 frontier

The preregistered cell `beta=[3261/32,3263/32]`, with
`lambda=[3/2,19/10]`, 115 modes, Taylor orders `(50,50)`, and 500 Arb bits,
terminated with `mean-value upper endpoint is not negative` after 138.5 s.
The runner produced only a `.failed.txt` traceback; no certificate or replay
transcript exists.

This is an enclosure-width failure, not a certified sign change. The frozen
configuration is retired for this cell. Any narrower successor must be
pre-registered separately; no retrospective parameter change is allowed.
G2 and G6 are unchanged.
