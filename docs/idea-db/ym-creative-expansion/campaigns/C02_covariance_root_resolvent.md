# Campaign C02 — covariance root through finite resolvent/Stieltjes calculus

## Goal
Attack the source hypothesis that a covariance root is localized.

## Candidate identity

```text
K^(-1/2) = (1/pi) * ∫_0^∞ s^(-1/2) * (K+sI)^(-1) ds
```

If `(K+sI)^(-1)` has a kernel bound uniform enough in `s`, integrate the bound to obtain root-kernel decay.

## Why this is new fuel
- Riemann repo supplies finite resolvent positivity and tail/rate style.
- Dimock source DB supplies Green/random-walk resolvent localization.
- THE-ERIKSSON-PROGRAMME already has exact covariance from coercivity and carries root localization explicitly.

## First experiment
Diagonal SPD matrix on `Fin n`; prove the identity scalarwise and derive a kernel bound. Then try self-adjoint diagonalization.
