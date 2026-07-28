# Positive-lane delta-six remainder contract

**Registered:** 2026-07-12, after the exact-series design engine reproduced
`r5` and derived the candidate `r6`, and before any uniform delta-six
remainder result  
**State:** `DESIGN_GATE`; exact target checker and G2 remain open

Conditional on the immutable checker reproducing

```text
r6(c) = (8148c^12+17095c^10+10768c^8+634576c^6-2557408c^4
          +2283296c^2-549376)/(131072c^18),
```

the strengthened sufficient target is fixed as

```text
abs(Y - T - r2 delta - r3 delta^2 - r4 delta^3
      - r5 delta^4 - r6 delta^5) <= 150000 delta^6
```

for `0<=delta<=1/20`, `1/sqrt(2)<=c<=1`.  A 2,000-box
outward-rounded budget sweep gives a worst allowed coefficient greater than
`153507.7` after charging `r4,r5,r6`, so the round integer `150000` has
strict pre-observation slack.

This target is unusable unless the separately manifested exact checker
passes.  It strengthens but does not supersede the registered `384 delta^4`
and `7600 delta^5` criteria.  No threshold may be increased after observing
a remainder run without a new dated registration.
