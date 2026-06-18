# Current State

**Last certified checkpoint:** 2026-06-18
(`feat(rg): prove fillings multiplicity bounds (P2b-ii-b-2 closed)`,
ledger Addendum 90).

This file is the short, live entry point. Historical plans and ledgers are kept
because they matter, but this page is the first place a new reader should look
before deciding what is actually proved and what remains open.

## Verified Core

* `lake build YangMillsCore` is green at **8264 jobs**.
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
* lattice animal counting, cube adjacency, and shell-growth summability.

The latest theorem is `YangMills.RG.lattice_exp_sum_le_geometric`: shell growth
`# {z : ell z = k} <= C*r^k` plus `r*exp(-sigma) < 1` gives the closed
summability constant `C*(1-r*exp(-sigma))^-1`.

## Live Frontier

The remaining hard input is still **not** a compiler trick:

* `hRpoly`: the concrete Yang-Mills single-scale activity-decay bound, i.e. the
  Dimock/Balaban cluster expansion with holes plus the fluctuation-integral
  estimate for the actual gauge RG operator.

The scaffolding around it is mostly theorem-fed. What is missing is the
model-specific constructive-QFT proof: concrete gauge-covariant operator,
background-field minimizer, propagator decay, localization, and the activity
bound that feeds the existing KP-with-holes/summability shell.

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
