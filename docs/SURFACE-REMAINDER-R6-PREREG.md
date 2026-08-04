# Positive-lane delta-five remainder contract

**Registered:** 2026-07-12, after manifested exact extraction of `r5` and
before any uniform delta-five remainder result  
**State:** `DESIGN_GATE`; no G2 promotion

With the exact coefficient

```text
r5(c) = (12940c^10+16077c^8+173288c^6-1300912c^4
         +1358400c^2-346112)/(262144c^15),
```

the terminal strengthened target is

```text
abs(Y - T - r2 delta - r3 delta^2 - r4 delta^3 - r5 delta^4)
    <= 7600 delta^5
```

for `0<=delta<=1/20`, `1/sqrt(2)<=c<=1`.  A 2,000-box outward-rounded
budget sweep gives a worst allowed coefficient greater than `7676.5` after
charging `r3,r4,r5`, so the integer 7600 is fixed with strict slack.

This strengthens but does not supersede the independently registered
`384 delta^4` target: a production result may pass either fixed sufficient
criterion, and the validator must name which.  Delta/t birth partitions,
absolute-error comparison, dependency provenance, and failure rules remain
unchanged.  Raising 7600 or 384 after observing remainder output requires a
new dated registration.
