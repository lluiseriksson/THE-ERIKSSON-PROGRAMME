# G2 mid-order order-24 repair extension: units 57--59

**Status:** preregistered extension; quarantined evidence only.

This extension applies the already isolated order-24 repair to the adjacent
quarter-width units 57--59:

```text
[125/2,251/4], [251/4,63], [63,253/4].
```

The only changed numerical parameter relative to order 22 is beta Taylor
order 24. `CWIN=3/2`, t order 25, 180-bit Arb precision, beta width 1/4,
and minimum t width `1/100000` are frozen. Every unit must have fresh
production and replay transcripts with byte equality and exact beta/t
adjacency. The resulting sign rows remain quarantined and cannot promote
`H_tail`, G2, G6, K2, or K4.
