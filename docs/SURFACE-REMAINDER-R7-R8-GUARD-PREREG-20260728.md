# R7/R8 over-order guard — preregistration (2026-07-28)

The exact-head checker registered at order nine has zero unused formal order:
it retains moment coefficients through `delta^8` and extracts `Y0,...,Y7`
after the exact division by `delta`.

Before promoting those heads, run the same expression-level engine with:

```text
series truncation O(delta^11)
relative companion degree 10
```

Acceptance requires:

- `B(0)=0` exactly;
- `KD(0)` is an exact nonzero expression;
- no `Float` occurs in any extracted coefficient;
- the first eight coefficients are exactly identical to the frozen
  `Y0,...,Y7` targets;
- both additional coefficients `Y8,Y9` are finite exact rational functions
  of `c`;
- production and replay print identical normalized mathematical lines.

This guard checks truncation stability, not mathematical independence of the
underlying model.  A pass does not certify the complex circle, true
companions, exterior, K2, or the manuscript.
