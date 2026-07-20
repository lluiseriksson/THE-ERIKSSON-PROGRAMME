# Incident: second half of the G2 frontier parent fails

The preregistered half-cell `beta=[6523/64,3263/32]`, with
`lambda=[3/2,19/10]`, modes 115, orders `(50,50)`, and 500 Arb bits,
terminated with `mean-value upper endpoint is not negative`. Only a
`.failed.txt` traceback was produced; no certificate or replay exists.

Together with the failed 1/32 parent, this retires the 1/64 configuration for
the upper half of the parent. It is an interval-enclosure failure, not a
certified sign change. Any 1/128 successor is a new preregistered experiment;
G2/G6 remain unchanged.
