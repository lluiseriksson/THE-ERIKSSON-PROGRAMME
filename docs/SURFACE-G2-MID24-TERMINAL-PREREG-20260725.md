# Terminal order-24 direct-sign cover for the remaining beta gap

Status: preregistered terminal attempt; no promotion until the complete
production/replay union and role audit pass.

The target is exactly `beta in [241/4,275/4]` and
`t in [3/5, pi-(3/2)/beta]`, partitioned into the quarter-width beta units
57 through 81. The fixed contract is CWIN `3/2`, beta Taylor order 24, t
order 25, 180 Arb bits, and minimum t width `1/100000`. No mesh or stopping
rule is changed.

Acceptance requires fresh terminal-wrapper production and replay for all 25
units, exact beta/t adjacency, strict negative row upper bounds, current
dependency hashes, and byte equality. The result is direct `W^J<0` evidence
only; it does not assert `(H_tail)` or G2/G6 closure.
