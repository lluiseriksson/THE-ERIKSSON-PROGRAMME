# Terminal order-24 direct-sign extension for the lower part of the beta gap

Status: preregistered terminal attempt; no promotion until production/replay,
the exact adjacency check, and the independent relay audit pass.

This extension covers exactly `beta in [241/4,125/2]`, partitioned into the
nine quarter-width units with indices 48 through 56.  It is the lower part
of the order-24 terminal cover whose upper extension is recorded in
`SURFACE-G2-MID24-TERMINAL-PREREG-20260725.md`.  The fixed contract is CWIN
`3/2`, beta Taylor order 24, t order 25, 180 Arb bits, and minimum t width
`1/100000`; no mesh or stopping rule is changed.

Acceptance requires fresh terminal-wrapper production and replay for all nine
units, exact beta/t adjacency, strict negative row upper bounds, current
dependency hashes, and byte equality.  The result is direct `W^J<0`
evidence only; it does not assert `(H_tail)` or G2/G6 closure.
