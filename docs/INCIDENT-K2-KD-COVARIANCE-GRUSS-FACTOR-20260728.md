# Incident — KD-covariance within-cell Grüss factor

**Date:** 2026-07-28

**Scope:** design probe only; no K2, K4, S1/S2, gate, or manuscript
promotion.

The first grid-48 run used

```text
weight_mass * a_radius * g_radius / 4
```

for the within-cell covariance charge.  Here `a_radius` and `g_radius` were
already center-deviation radii:

```text
|A-A_center| <= a_radius,
|G-G_center| <= g_radius.
```

Their range widths are therefore at most `2*a_radius` and `2*g_radius`.
Grüss gives one quarter of the product of the *widths*, namely

```text
|Cov(A,G)| <= a_radius*g_radius,
```

with no further division by four.  The initial transcript with SHA-256
`8A1E65F310E8A2B39C1426D47D41C22595C819F0DACE0027DFA7DFD0FEC1FBAF`
(raw CRLF) and
`B7BC855A751AD7E348E02D558F27E7AF8D720EB9411E3651C712FEE6F8A9B8CF`
(normalized LF) is preserved under a `SUPERSEDED-GRUSS-QUARTER` filename
and carries no design load.

The helper now names the bound explicitly and has a regression test.  The
same frozen grid, precision, target, and pass predicate are rerun after this
correction.  Even a corrected pass authorizes only higher-order design work;
it does not discharge companion, exterior-tail, or positive-delta
uniformity obligations.
