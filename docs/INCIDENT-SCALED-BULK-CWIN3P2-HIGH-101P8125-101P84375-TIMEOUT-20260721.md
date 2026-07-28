# Finite-beta seam diagnostic timeout

**Date:** 2026-07-21  
**Scope:** diagnostic only; no G2/G6 promotion

The preregistered CWIN=`3/2` high-order scaled sign-row unit

```text
beta in [3258/32,3259/32] = [101.8125,101.84375]
beta_order=30, t_order=37, Arb=180 bits, min_dt=1/100000
```

was run from the existing cached backend for five minutes.  It produced no
terminal row or sign verdict before the fixed operational timeout (`exit 124`).
No transcript, manifest, or coverage claim was created.  The timeout confirms
that this fixed unit is still conditioning-limited at the registered
`min_dt` wall; it is not evidence of a mathematical sign failure.

An isolated tail-width experiment rebuilt the same box with Fourier cutoff
`M=beta+85` (rather than the registered `beta+55`), preserving the same
derivative majorants.  It reached the enlarged `M=186` construction but also
timed out after five minutes before a single terminal row.  The extra tail
width is therefore retired as a practical rescue; it is not a certified
result and does not alter the registered contract.

The same order-30 contract was re-run in isolation on 2026-07-24 and again
failed near `t=3.126555800582593` after roughly 523 seconds. A separate
preregistered sine-normalized order-40/45 route then passed its local stress
box but timed out on the exhaustive unit; its result is recorded in
`INCIDENT-SCALED-BULK-SIN-NORMALIZED-101P8125-101P84375-TIMEOUT-20260724.md`.

The candidate finite-beta union therefore remains `[20,101.8125]` with the
unresolved seam `[101.8125,1000/9]`. Further progress requires a new
algebraic/grouped evaluator or an analytic majorant; repeating either frozen
contract or silently subdividing the unit is not authorized.
