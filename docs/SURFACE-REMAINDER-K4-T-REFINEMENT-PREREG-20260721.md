# K4 fixed-width t refinement probe

This candidate probe is registered before reading the next result. It keeps
the manifested positive-delta band

```text
delta = [1/25,81/2000]
```

and the frozen centred integrator (`seed_grid=12`, `max_cells=9216`, 140 Arb
bits). The only new partition is the fixed rational `t` ladder of width
`1/100` beginning at `9/4`; the first unit is `[9/4,113/50]` (`[2.25,2.26]`).

Each unit requires a production transcript, an independent replay, exact
cell coverage, and all seven literal fractions strictly below one. A failed
unit is retained as a negative design result; no unit width, grid, or budget
may be changed in response. Even a green ladder would remain candidate-only:
the regular δ=0 patch, global delta/t union, overlap, and weighted
S1'''/S2''' assembly are separate obligations.

## Fixed continuation

Before reading the first refined result, the next two exact boxes are fixed
as `[113/50,227/100]` and `[227/100,57/25]`. They use the identical
integrator, cell limit, precision, and replay rule. No narrower or wider box
is admitted in response to their results.

The next fixed continuation is `[57/25,229/100]` followed by
`[229/100,23/10]`, again with no parameter changes after observation.
