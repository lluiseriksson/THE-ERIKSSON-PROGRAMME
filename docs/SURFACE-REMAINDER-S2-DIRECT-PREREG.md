# Direct joint-remainder route for G2 — pre-registration

**Registered:** 2026-07-12, before any uniform parameter-box run

**State:** `DESIGN_GATE`; no certificate claim

The earlier S2''' weighted-second-derivative criterion is sufficient but not
necessary.  This record fixes a more direct terminal target already named in
the manuscript as the sharp joint bound.  It does not reuse the defective
full-torus carrier from `INC-S2-FULL-TORUS-CARRIER.md`.

## Fixed target

Let `Y=X_main/delta` be the repaired main-saddle carrier on the exact physical
square `[0,6/5]^2`, let `delta=1/beta`, `c=cos(t/4)`, and use the manuscript's
closed forms `T(c)`, `r2(c)`, and `Theta3(c)`.  The candidate relay threshold
is fixed here as

```text
beta1 = 20,       delta1 = 1/20.
```

The terminal inequality is

```text
abs(Y(delta,t) - T(c) - r2(c)*delta) <= Theta3(c)*delta^2
```

for every `0 <= delta <= 1/20` and every
`0 < t <= pi-(3/2)delta`.  Multiplication by `delta` gives the joint remainder
bound for `X_main`; hence it absorbs the extracted and unextracted chains in
one `Theta3` bucket and discharges `(H_tail)` without a separate estimate of
`Y''`.

The already disclosed design values at `t=2.9` and beta 15, 20, 30 motivated
testing this route.  They are not terminal evidence and must not determine a
posterior mesh, tolerance, or exception.

## Terminal contracts

1. `R0` — the carrier is assembled only from exact Arb enclosures of
   `KD,KF,HDD,HDF`; centering may choose any delta-jet because the bilinear
   numerator is algebraically invariant, but the identity is tested.
2. `R1` — every parameter box proves `KD>0`; an unresolved denominator fails.
3. `R2` — the `(delta,t)` boxes are born ordered and cover the full curved
   domain without gaps.  The moving boundary is rounded outward.
4. `R3` — every nonzero-delta box proves the displayed residual inequality by
   outward-rounded arithmetic.  Multiprecision quadrature and point values are
   audits only.
5. `R4` — a separate analytic Taylor/entire-series patch contains `delta=0`.
   No `1/delta` interval may cross zero, and no finite-difference derivative is
   certificate evidence.
6. `R5` — the run prints script hash, commit, versions, effective boxes and a
   terminal verdict; a manifest owns its transcript and an executable
   validator checks adjacency and the exact claim.

Failure of any contract leaves G2 open.  Raising `beta1`, weakening the
inequality, or excluding a parameter subrange requires a new dated
pre-registration.  The mirror and completion costs remain in G1/K4 and may
not be silently folded into this carrier.
