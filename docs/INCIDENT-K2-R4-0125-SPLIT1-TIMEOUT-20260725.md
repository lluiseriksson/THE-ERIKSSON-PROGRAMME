# Incident — K2 exact-r4 delta=1/80 split 1 timeout

Date: 2026-07-25. The second preregistered physical-inner split
`1183/1000` of the delta-`1/80` three-witness design was run in a fresh
process with the frozen witnesses `(0,384),(50,192),(157,384)`, Arb-140, and
the registered core/annulus partition. The command exceeded the 600-second
wall-clock limit without producing a transcript or a witness margin.

This is an inconclusive timeout, not a negative certificate and not a proof of
the K2 inequality. The split is rejected for design progression because the
contract requires all three witnesses to return strict positive margins before
an exhaustive cover may start. No K2, `(H_tail)`, G2, or G6 promotion follows.
