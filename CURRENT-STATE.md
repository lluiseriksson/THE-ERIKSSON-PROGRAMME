# Current State

**Last certified checkpoint:** 2026-06-19
(`feat(RG): bound skeleton-pinned cluster remainder sums`).

This file is the short, live entry point. Historical plans and ledgers are kept
because they matter, but this page is the first place a new reader should look
before deciding what is actually proved and what remains open.

## Verified Core

* `lake build YangMillsCore` is green at **8273 jobs**.
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
* polymer-with-holes multi-hole combinatorics, multiplicity bounds, discrete
  modified-metric summability, and the cluster-union modified-metric interface.

The latest RG theorem is `YangMills.RG.clusterSkeletonRemainderSum_tsum_le`:
under the tilted KP criterion for `holePolymerSystem H z`, the full
skeleton-pinned cluster remainder series is bounded by a finite pinned sum of
tilted activity weights over polymers whose active skeleton contains the root.
Together with `clusterSkeletonRemainderSum_term_le_skeletonPinned`,
`clusterSkeletonRemainderSum_term_le_pinned`,
`clusterSkeletonRemainderSum_summable`, `clusterUnionPolymer`, and
`clusterUnion_skeleton_card_le_clusterModifiedMetric_add_one`, this gives a
source-shaped cluster object, skeleton-pinned summability, and a quantitative
KP bound later `hRpoly` activity-decay work can consume.

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

The reusable F2 substrate now also includes
`ContinuousUnitaryMatrixRep`: a continuous homomorphism into Mathlib's unitary
matrix group, with continuous matrix coefficients, finite-measure Haar `L²`
vectors, a continuous character, and conjugation invariance. Its
`toRepresentation` bridge exposes Mathlib's algebraic irreducibility and
intertwiner API; consequently, intertwiners between irreducibles are zero or
bijective and self-intertwiners are scalar. The defining representation
`fundamentalUnitaryRep` instantiates the analytic API. Haar averaging now turns
an arbitrary matrix into an intertwiner: it vanishes between inequivalent
irreducibles and is scalar within one irreducible. Probability-Haar trace
normalization identifies the scalar exactly, giving coefficient inner products
`δᵢₖ δⱼₗ / dim ρ`. Thus generic Schur orthogonality is theorem-fed for this
matrix-realized irreducible API. Peter-Weyl completeness remains open.

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
