# Unit-82 point probe at the failed minimum-step boundary

**Status:** diagnostic only; no finite-cover, H-tail, G2, or G6 promotion.

The order-24 campaign failed to certify the final beta unit
`[275/4,69]` at a minimum `t` step near
`t=3.1178733989897687`.  A separate high-order point probe was run with the
scaled backend, Arb precision 220, beta order 30, and `t` order 35.  It used a
`10^-12` beta neighbourhood around each exact test beta and evaluated the
same normalized Wronskian enclosure at the exact rational `t` point:

```text
beta = 275/4   W^J = [-5.6470669438e-75 +/- 5.54e-86]
beta = 551/8   W^J = [-4.2329648890e-75 +/- 1.91e-86]
beta = 69      W^J = [-3.17295643854e-75 +/- 8.39e-87]
```

All three point intervals are strictly negative, so this probe does not
falsify the normalized sign conjecture at the reported point.  It also does
not repair the failed interval cover: a point value cannot certify the whole
cell, and it says nothing about the separate absolute `(H_tail)` relay or its
missing `M_supremum` budget.  The unit remains quarantined.

Probe script SHA-256: `84b81cf28d4c27ed9409fac08893c7dfd3f807ba4b747ddaa63eaf38d189e8c1`.
