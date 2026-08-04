# Incident: standard bridge boundary at `[101.8125,101.84375]`

**Date:** 2026-07-20  
**Scope:** candidate finite-beta bridge only; no theorem or gate promotion

The exact successor unit
`[1629/16,3259/32]=[101.8125,101.84375]` was preregistered with the
unchanged CWIN=`3/2`, beta-order 30, t-order 37, 180-bit Arb, and
`min_dt=1/100000` contract.  Production reached the frozen minimum t width
and stopped at

```text
RuntimeError: bulk failure near t=3.126555800582593
```

No terminal transcript or replay was produced, so the unit is not evidence.
The preceding paired units remain valid only on their own domains and the
candidate topology currently ends at `beta=1629/16`.  This is a conditioning
boundary of the present interval representation, not a sign counterexample.
Further work over the remaining `[1629/16,1000/9]` interval requires a new
analytic or asymptotic contract; unregistered subdivision, extrapolation, or
promotion is forbidden.
