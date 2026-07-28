# G5 extension on the terminal G2 frontier (2026-07-26)

## Scope

This preregisters a finite five-family right-edge cover on the exact beta
interval still missing from the direct scaled-bulk union:

```text
beta in [3409/32, 1000/9]
delta in [9/1000, 32/3409]
lambda = beta*(pi-t) in [3/2, 2]
```

The existing G5 certificate covers `lambda<=3/2`.  The purpose here is to
cover the adjacent strip `3/2<=lambda<=2`, which contains the cancellation
cell where the scaled bulk evaluator loses resolution.  This is a candidate
extension only until production, replay, geometry, and the exact seam audit
all pass.

## Frozen analytic contract

1. Use the exact divided-difference five-family formula for `P0` and `H`.
2. Use one delta band `[9/1000,32/3409]` and 25 adjacent lambda cells of
   width `1/50`, `[3/2,2]`.
3. Recompute the near-tail budget with `exp(lambda_max)=exp(2)`; the old
   `exp(3/2)` charge is forbidden.  The far-exterior budget and the Bessel
   companion contract are reused only after the explicit geometry checks below.
4. Check the existing chart inequalities and additionally prove, with exact
   rational/Arb comparisons, `delta_max*lambda_max/2 < 1/100 < 3/80`.
   Consequently every shifted chart remains inside the previously audited
   finite geometry, and the phase residual is bounded by `lambda_max=2`.
5. Every cell must have strict outward-rounded lower endpoints `B0>0` and
   `P0>0`; otherwise the extension is rejected.

Even a complete pass has no automatic G2/G6 load.  The final relay must audit
the exact map `lambda=beta*(pi-t)`, overlap at `lambda=3/2`, and the two beta
seams before any gate promotion.
