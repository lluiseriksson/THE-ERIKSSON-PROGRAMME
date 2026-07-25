# Incident — exact-r4 K2 widening loses the denominator sign

**Date:** 2026-07-25  
**Probe:** serial single-cell stress box, `t=[72/25,29/10]`, index 144,
grid 192, Arb precision 140.

The existing exact-r4 regular judge was called with wider endpoint lanes
`delta_max = 1/100`, `1/80`, and `1/50`.  All three attempts failed before
forming the quotient with:

```text
ValueError: leading term in denominator is not nonzero
```

This is a genuine enclosure failure, not a negative margin and not a proof of
the underlying inequality.  The current exact-r4 architecture therefore
cannot simply be widened past its registered small-delta lane; it needs a
new centred denominator carrier or a separate positive-delta construction.
No K2/G2/G6 state changes and no transcript was produced.
