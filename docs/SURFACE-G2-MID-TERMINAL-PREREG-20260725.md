# Terminal direct-sign cover for the first beta gap

Status: preregistered terminal attempt; no promotion until production,
replay, and the role audit pass.

The target is exactly `beta in [193/4,225/4]` and
`t in [3/5, pi-(3/2)/beta]`. The frozen repair uses CWIN `3/2`, beta Taylor
order 22, t order 25, 180 Arb bits, minimum t width `1/100000`, and beta
boxes of width `1/4` (32 units). No endpoints, mesh, or stopping rule may be
changed.

Acceptance requires fresh production and replay transcripts, exact beta and t
adjacency, strict negative row upper bounds, current dependency hashes, and a
terminal direct-sign scope. The resulting rows prove only `W^J<0` on this
compact domain; they do not assert `(H_tail)` or G2/G6 closure.
