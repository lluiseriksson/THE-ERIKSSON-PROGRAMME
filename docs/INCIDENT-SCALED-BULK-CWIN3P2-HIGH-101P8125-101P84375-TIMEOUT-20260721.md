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

The candidate finite-beta union therefore remains `[20,101.8125]` with the
unresolved seam `[101.8125,1000/9]`.  Further progress requires a new
algebraic/grouped evaluator or an analytic majorant; repeating this same
contract or silently subdividing the unit is not authorized.
