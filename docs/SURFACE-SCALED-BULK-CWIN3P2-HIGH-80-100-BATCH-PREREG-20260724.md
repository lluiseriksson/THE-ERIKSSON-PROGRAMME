# High-order scaled bulk batch `[80,100]` — preregistration

**Registered:** 2026-07-24, before the batch continuation

This batch addresses the unresolved finite-beta gap with the already frozen
high-order evaluator.  It is divided into the exact quarter-width units

```text
[80+ j/4, 80+(j+1)/4],  j=0,...,79.
```

Every unit uses `CWIN=3/2`, beta order `30`, t order `37`, `min_dt=1/100000`,
180 Arb bits, and the moving domain
`[3/5, pi-(3/2)/beta_hi]`.  Each production/replay pair must pass the
existing ordered sign-row validator with byte-identical output and fresh
dependency hashes.  A failed unit is retained as a negative incident and
does not license widening or order changes.

The entire batch remains candidate sign evidence.  Even a complete batch
would not by itself prove the absolute `(H_tail)` relay, K2/K4, S1'''/S2''',
or promote G2/G6; those gates require their separately registered analytic
and weighted contracts.
