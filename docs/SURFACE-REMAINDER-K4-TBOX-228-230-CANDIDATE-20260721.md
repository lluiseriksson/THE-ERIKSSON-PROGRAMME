# K4 refined t-box tail `[2.28,2.30]`

The fixed width-`1/100` continuation passes on both adjacent boxes
`[57/25,229/100]` and `[229/100,23/10]`. Each uses 9,216 cells, 140 Arb bits,
and the frozen centred integrator; production and replay are byte-identical.
The worst literal fractions are `0.2067745517...` and `0.1916942546...`.

This closes only a local candidate t strip on one positive-delta band. The
regular δ=0 patch, all remaining parameter boxes, overlap, and the weighted
S1'''/S2''' union are still absent, so no K4 or G6 promotion is made.
