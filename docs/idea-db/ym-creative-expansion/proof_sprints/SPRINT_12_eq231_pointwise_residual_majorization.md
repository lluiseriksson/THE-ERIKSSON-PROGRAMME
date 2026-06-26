# Sprint 12 — Eq. (2.31) pointwise P-residual majorization

## Precondition

Do this only after at least the P dictionary/carrier route is source-shaped.

## Target shape

```text
pResidualWeight(Z,D,P)
  <= A231 * pGeometryWeight(Z,D,P)
  <= A231 * exp(-rho*gapMass(Z,D))*exp(-2*rho*|P|)
```

## Existing Lean consumer

The entropy sum is already handled by the Eq. (2.31) PWeight machinery. The
missing part is pointwise identification of the residual term and geometry
weight.

## Fail condition

Any proof that jumps from the finite sum bound to a termwise estimate is invalid.
