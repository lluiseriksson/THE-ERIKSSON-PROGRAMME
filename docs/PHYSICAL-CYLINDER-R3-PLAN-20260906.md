# R3: physical reflected positivity and a nonzero centered sector

Registered on 6 September 2026 after the scoped R2 source milestone at
[`507e8a38ce7f7addf9c1b8f65d296dc00b77971b`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/commit/507e8a38ce7f7addf9c1b8f65d296dc00b77971b).
This is a proof plan, not a new compiled result. All R3 obligations remain open.

R2 supplies the actual SU(2) cylinder measure and reflected integral, with
both crossing links present. R3 must prove positivity for that same integral
and construct a strictly positive centered physical norm. Neither property
may be received as a hypothesis or hidden in a structure field.

## Existing ingredients: do not rebuild them

The mother's `OS/SU2WilsonReflectionKernel.lean` already provides
`su2WilsonCrossing_isHaarPSDKernel`, continuous positive finite-rank
presentations, their product/sum/scale closure, positive Taylor approximants,
uniform convergence and integral convergence. Use those results for the
two-link product kernel, with explicit pullbacks to the slice coordinates.

`OS/SU2WilsonReflectionSharp.lean` already supplies the Haar-zero fundamental
character, Schur entry moments, and `su2Trace_crossing_lower` with bound
`beta/4`. Reuse the analytic facts. Its one-link observable and the auxiliary
endpoint do not themselves prove the cylinder's spatial-loop norm. The
frozen auxiliary modules remain unchanged.

The [ARR reuse audit](PHYSICAL-REFLECTION-REUSE-AUDIT-20260906.md) remains
applicable: do not recreate the satellite's Haar, character/convolution or
disk-amplitude theory. The cylinder has Euler characteristic zero, so its
identification with the certified disk record is unavailable.

## Required physical identifications

Write a spatial slice as `u=(u0,u1)` and a vertex gauge element as
`a=(a0,a1)`. The action already used in R2 is
`T_a(v)=(a0*v0*a1^-1, a1*v1*a0^-1)`.
Let `P f(v)` be its average over the two Haar gauge variables and let
`K_beta(u,v)=w_beta(u0*v0^-1)*w_beta(u1*v1^-1)`.

The proposed proof must establish all of the following identities for
continuous complex observables, with integrability and measure preservation:

1. `P` is an idempotent self-adjoint gauge average on the slice Haar measure.
2. The literal R2 density gives the product kernel evaluated at `u,T_a(v)`.
3. The kernel is invariant under the same vertex gauge action on both slices.
4. The normalized physical reflected form equals the positive product-kernel
   form applied to `P f` on **both** sides (with orientation/conjugation matched).

A form with `f` on one side and `P f` on the other is not sufficient without
the commuting-projection identity. Positivity of each fixed-gauge twisted
kernel is not assumed. These are targets to prove, not accepted rewrites.

## Milestones and acceptance

| Step | Required output | Status |
|---|---|---|
| R3a | Slice gauge measure preservation, averaging identities and the literal physical-to-product-kernel identity | Open |
| R3b | Real nonnegative physical quadratic form for every continuous complex observable at `beta >= 0`, hence finite complex Gram positivity | Open |
| R3c | Exact physical slice marginal and centering of a chosen spatial-loop observable | Open |
| R3d | A derived strictly positive physical reflected norm for that centered observable at `beta > 0` | Open |

The candidate observable is `trace(u0*u1)`. Its gauge invariance, physical
mean and reflected norm must be proved on the cylinder; nonconstancy alone
does not suffice. Reuse Schur moments and positive Taylor features to obtain
a lower bound, keeping the actual partition normalization visible. No
numerical constant is accepted in advance. The `beta=0` case must be kept
separate: Haar independence eliminates centered reflected fluctuations.

All compilation, oracles and sustained checks run in prepared task-owned
CPU/high-RAM Colab units, with release after completion and complete evidence
preservation. New headlines require focal compilation, a green unchanged
core and individual axiom readouts. Preserve failed diagnostics. The R2
saved-log parser lesson applies to primed Lean names. Full global validation
and terminal same-SHA reproduction remain distinct scopes.

This finite SU(2) cylinder does not establish arbitrary finite-lattice
reflection positivity, the R4 transfer/quotient construction, R5 observable
totality and clustering identification, or a 4D continuum limit and mass
gap for every compact simple gauge group. hRpoly remains a separate task.
Historical Clay label: **~0% (<0.1%)**, not a measured percentage.
