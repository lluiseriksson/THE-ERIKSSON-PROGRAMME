# Incident: wide lambda cell rejected (2026-07-22)

The preregistered cell

```text
beta   [13059/128,13060/128]
lambda [2,3]
modes 115; beta/lambda orders 50/50; Arb 500 bits
```

was run by the unchanged mean-value driver.  The strict upper-endpoint test
failed (`RuntimeError: mean-value upper endpoint is not negative`), so no
production or replay certificate was emitted.  The failure is a dependency
loss in the wide lambda box, not a numerical sign counterexample.

This rejects the one-box `[2,3]` continuation.  Any future direct-`W` route
must preregister narrower lambda cells; no order, precision, or boundary was
changed in response, and no G2/G6 promotion follows.
