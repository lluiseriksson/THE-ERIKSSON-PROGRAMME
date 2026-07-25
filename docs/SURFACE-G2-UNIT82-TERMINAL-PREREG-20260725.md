# Terminal direct-sign cover for the last beta gap

Status: preregistered terminal attempt; no promotion until the full validator
and role audit pass.

This contract targets exactly
`beta in [275/4,69]` and `t in [3/5, pi - (3/2)/beta]`. It uses the already
identified stable rescue representation: CWIN `3/2`, beta Taylor order 30,
t order 35, 220 Arb bits, and minimum t width `1/100000`, with the beta
partition `[275/4,1101/16]`, `[1101/16,1103/16]`, and
`[1103/16,69]`.

Acceptance requires fresh production and replay runs from the terminal
wrappers, byte-identical transcripts, current dependency hashes, strict
negative Arb row upper bounds, exact t adjacency within each slice, and exact
beta adjacency across the three slices. The transcript scope must identify
the direct `W^J<0` claim and must not claim `(H_tail)`.

Even if this cover passes, it can replace the finite scaled-bulk slot only
after the independent algebra and role audits establish the direct-sign relay
and Theorem A supplies the denominator positivity. It does not close K2, K4,
S1'''/S2''', or G6 by itself.
