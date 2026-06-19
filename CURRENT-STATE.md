# Current State

**Last certified checkpoint:** 2026-06-19
(`feat(ClayCore): prove fundamental SU(N) Schur orthogonality and its Haar L2 form`,
 ledger Addendum 106).

This file is the short, live entry point. Historical plans and ledgers are kept
because they matter, but this page is the first place a new reader should look
before deciding what is actually proved and what remains open.

## Verified Core

* `lake build YangMillsCore` is green at **8271 jobs**.
* `lake env lean oracle_check.lean` prints only
  `[propext, Classical.choice, Quot.sound]` for every headline theorem.
* `python scripts/check_consistency.py` enforces zero `sorry` in the proof tree
  and zero `axiom` declarations in the verified-core source tree.
* Lean is fixed by `lean-toolchain`; Mathlib is pinned to commit
  `07642720480157414db592fa85b626dafb71355b` in both `lakefile.lean` and
  `lake-manifest.json`.

## What Is Theorem-Fed

The strong-coupling lattice side is now extensive and oracle-clean:

* sharp Kotecky-Preiss / Mayer-Ursell cluster expansion;
* polymer reconstruction `Z = Xi = exp(K)`;
* volume-uniform exponential clustering for local Gibbs observables;
* finite-volume, exact-activity, and volume-uniform Wilson-loop area laws;
* the lattice mass-gap assembly with the IR side theorem-fed;
* the gauge-RG conditional scaffold from Balaban/Dimock-style inputs to the
  lattice UV hypothesis.

## RG Substrate Now Proved

The `YangMills/RG/**` layer contains a verified continuum-facing substrate:

* block geometry and the linear averaging operator `Q`;
* gauge covariance of the averaged-contour interface;
* near-identity logarithm and small-field stability lemmas;
* explicit l2 contraction of `Q`;
* free Gaussian covariance pushforward and finite-dimensional Gaussian
  construction;
* marginal-coupling summability and conditional UV mass-gap assembly;
* exponential-decay kernel calculus, Schur bounds, PSD kernel interface,
  Gaussian MGF bounds;
* lattice animal counting, cube adjacency, and shell-growth summability;
* polymer-with-holes multi-hole combinatorics, multiplicity bounds, and discrete modified-metric summability.

The latest theorem is `YangMills.RG.discreteModifiedMetric_weight_summable`: polymer sum over connected, hole-respecting polymers containing $r$ in their skeleton weighted by $q^{d_M(X) + 1}$ is bounded volume-uniformly by $(1 - 3^{2d} \cdot q \cdot 2^{3^d + 1})^{-1}$ when $3^{2d} \cdot q \cdot 2^{3^d + 1} < 1$.

## Live Frontier

The remaining hard input is still **not** a compiler trick:

* `hRpoly`: the concrete Yang-Mills single-scale activity-decay bound, i.e. the
  Dimock/Balaban cluster expansion with holes plus the fluctuation-integral
  estimate for the actual gauge RG operator.

The scaffolding around it is mostly theorem-fed. What is missing is the
model-specific constructive-QFT proof: concrete gauge-covariant operator,
background-field minimizer, propagator decay, localization, and the activity
bound that feeds the existing KP-with-holes/summability shell.

Independently, the fundamental representation now has exact Schur
orthogonality in Haar `L²`:
`inner_fundamentalMatrixCoeffL2` proves the coefficient inner products
`δᵢₖ δⱼₗ / N`, and
`orthonormal_normalizedFundamentalMatrixCoeffL2` packages the normalized
coefficients as an orthonormal family. Generic compact-group Peter-Weyl and
generic irreducible representations remain open.

## What Is Not Claimed

There is **no continuum limit**, **no Osterwalder-Schrader/Wightman
reconstruction**, and **no continuum Yang-Mills mass gap** in this repository.
Everything above is lattice-side strong-coupling mathematics and conditional
continuum-facing scaffolding. Distance to the Clay Millennium problem remains
**~0% (<0.1%)**.

## Best Next Work

1. Build the concrete YM activity-decay campaign for `hRpoly` from primary
   Balaban/Dimock sources.
2. Keep the RG operator/propagator work source-grounded and oracle-clean.
3. Do not introduce axioms or placeholder interfaces for the missing analytic
   theorem; carry gaps only as explicit theorem hypotheses.
