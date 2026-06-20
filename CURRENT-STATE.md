# Current State

**Last certified checkpoint:** 2026-06-19, updated through the latest
oracle-clean public `origin/main` commit (see `git log` and
`docs/VERIFICATION-LEDGER.md`).

This file is the short, live entry point. Historical plans and ledgers are kept
because they matter, but this page is the first place a new reader should look
before deciding what is actually proved and what remains open.

## Verified Core

* `lake build YangMillsCore` is green at **8283 jobs**.
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
* Hilbert-space adjoint mass for the averaging operator:
  `scaledLinAvgCLM`, `qMassCLM = Q†Q`, `inner_qMassCLM_self`,
  `qMassCLM_psd`, and `qMassCLM_opNorm_le`, formulated on the bond
  `ℓ²`/`PiLp 2` spaces with the rescaling scalar left explicit;
* gauge covariance of the averaged-contour interface;
* near-identity logarithm, small-field stability lemmas, and the local
  two-sided cutoff dictionary `norm_nearLog_two_sided_of_norm_le_third`,
  converting `‖Y‖ ≤ 1/3` into mutual control of `Y` and `nearLog Y` up to the
  constant `2` for the faithful variable `Y = D - 1`;
* explicit l2 contraction of `Q`;
* free Gaussian covariance pushforward and finite-dimensional Gaussian
  construction;
* marginal-coupling summability and conditional UV mass-gap assembly;
* the explicit producer/consumer split for the UV scalar estimate:
  `RawYMActivityDecay`, `RenormalizedHoleActivityDecay`, and
  `SingleScaleUVDecay`, with
  `singleScaleUVDecay_of_renormalizedHoleActivities` bridging with-holes
  activities to the scalar bound consumed by `UVMassGap`;
* the type-local functional/activity substrate
  `YangMills/RG/LocalFunctional.lean`: restricted fields indexed by finite
  supports, `LocalFunctional`, two-field `LocalActivity`, global adapters
  invariant under off-support changes, and finite products supported on support
  unions;
* the ultralocal product-measure factorization substrate
  `YangMills/RG/UltralocalFactorization.lean`: disjoint `LocalFunctional`
  supports, and disjoint `LocalActivity` fluctuation supports for fixed
  spectator field, factorize under an explicit finite product probability
  measure;
* the Mayer-cover factorization bridge
  `YangMills/RG/MayerCoverFactorization.lean`: two finite raw-Mayer cover
  products factorize under that product fluctuation measure whenever their
  fluctuation supports are pairwise disjoint, and a disjoint union of cover
  indices integrates as the product of the two integrated subcover products
  under the same cross-support disjointness hypothesis.  The same module now
  defines the fluctuation-overlap graph on cover indices and proves the
  no-cross-edge criterion that supplies that pairwise disjointness hypothesis;
  it also defines finite confined components, splits a cover `K` into the
  component of a root and its complement inside `K`, and now packages the full
  finite component decomposition: confined components cover `K`, intersecting
  components coincide, and distinct components are disjoint.  The same finite
  partition now feeds an n-ary Mayer-cover integral factorization over all
  confined components at once.  Each confined component is also proved
  walk-connected and can be repackaged as an `OmegaConnectedCover`, so the
  disconnected-component compiler can hand its finite blocks back to the
  source-shaped Ω-cover API; distinct confined components of the Ω-overlap
  graph also have pairwise disjoint active supports inside Ω;
* the raw Mayer local transform `YangMills/RG/RawMayerWithHoles.lean`:
  `H ↦ exp H - 1` on `LocalFunctional` and `LocalActivity`, support
  preservation, off-support invariance, and the elementary small-activity bound
  `‖exp z - 1‖ ≤ 2‖z‖` for `‖z‖ ≤ 1`;
* the Ω-connected Mayer-cover substrate
  `YangMills/RG/OmegaConnectedCover.lean`: Ω-overlap graph on cover indices,
  `OmegaConnectedCover`, and the finite product
  `∏ᵢ (exp Hᵢ - 1)` as a type-local `LocalActivity` whose spectator and
  fluctuation supports are the corresponding unions;
* the abstract activity-limit bridge
  `activity_profile_bound_of_tendsto`: a metric/profile bound uniform in a
  regulator passes to the pointwise limiting activity.  The same module also
  contains the telescopic regulator bridge
  `activity_profile_bound_of_tendsto_telescope`: if the initial activity has
  amplitude `amp` and the profile-weighted increments have summable budget
  `S`, then the pointwise limit has amplitude `amp + S`;
* exponential-decay kernel calculus, Schur bounds, PSD kernel interface,
  Gaussian MGF bounds, and the collar-separated cross-sum bound
  `expDecay_separated_finset_sum_le`: an `ExpDecay` covariance kernel pays
  `exp(-κ ε)` across a separated collar, the algebraic core needed by the
  Gaussian collar-factorization route inspired by Lluis Eriksson's
  `2512.0064v1` outlook;
* lattice animal counting, cube adjacency, and shell-growth summability;
* polymer-with-holes multi-hole combinatorics, multiplicity bounds, discrete
  modified-metric summability, and the cluster-union modified-metric interface.
* a source-facing active with-holes polymer system
  `omegaHolePolymerSystem`, whose incompatibility is intersection of active
  skeletons (`X₁ ∩ Ω` with `X₂ ∩ Ω`), matching Dimock II Appendix F's
  `Ω`-connected relation and kept separate from the existing touching
  hard-core `holePolymerSystem`;
* the corresponding source-facing local KP consumer
  `omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp` and
  convergence/norm companions: a local window pinned at each active skeleton
  cube feeds the KP criterion for the Ω-active Appendix-F relation;
* `omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp_of_metric_bound`,
  which derives that active local KP window from the pointwise modified-metric
  majorant `exp(t)‖z(Y)‖exp(|Y|) ≤ A q^(d_M(Y)+1)` and the already-proved
  discrete modified-metric summability, with direct convergence and
  cluster-sum norm-bound companions for the same metric-bound hypotheses.
* the matching Appendix-F-facing skeleton-pinned cluster-tail consumer
  `omegaClusterSkeletonRemainderSum_tsum_le_metric_bound`: the literal
  `Ω`-connected cluster relation now has a source-shaped `tsum` remainder
  bound under the same pointwise modified-metric activity majorant.
  The intermediate local-window forms
  `omegaClusterSkeletonRemainderSum_summable_of_local` and
  `omegaClusterSkeletonRemainderSum_tsum_le_of_local` are also available for
  sources that provide a polymer norm/local KP estimate directly, without first
  rewriting it into an explicit pointwise `q^(d_M+1)` majorant.  The uniform
  local-window forms
  `omegaClusterSkeletonRemainderSum_summable_of_uniform_local` and
  `omegaClusterSkeletonRemainderSum_tsum_le_of_uniform_local` further package
  the common source shape `local active-skeleton norm ≤ B ≤ 1` into the
  tail bound `≤ t⁻¹ B`.
* the abstract approximate-Ward cancellation layer
  `YangMills/SUSY/WardComplex.lean`: if an activity decomposes as `H = QB + R`,
  the `Q`-exact contribution is killed up to a quantitative defect before
  norms are applied, with pointwise profile consumers for polymer activities.
* the Ward-cancelled polymer bridge `YangMills/SUSY/WardPolymer.lean`: finite
  Ward-defect sums, integrated activities `wardActivity`, and exact/approximate
  Ward consumers feeding `omegaClusterSkeletonRemainderSum_tsum_le_metric_bound`
  for the literal `Ω`-active skeleton-tail system.

The latest RG skeleton-tail interface is local-KP-shaped throughout:

* `YangMills.RG.clusterSkeletonRemainderSum_summable_of_local` proves
  summability of the skeleton-pinned cluster remainder series from the tilted
  local activity-sum window;
* `YangMills.RG.clusterRemainderSum_summable_of_local` proves the analogous
  raw-union-pinned cluster remainder summability from the same tilted local
  activity-sum window;
* `YangMills.RG.clusterRemainderSum_tsum_le_of_local` proves the corresponding
  quantitative raw-union-pinned bound from that same window;
* `YangMills.RG.clusterRemainderSum_term_le_tilt` packages the raw termwise
  `exp(t)` tilt domination consumed by both raw-tail theorems, using the
  reusable KP lemma `YangMills.KP.orderFactor_pinnedClusterWeight_le_tilt`;
* `YangMills.KP.scaleActivity_exp_norm_activity_mul_exp`,
  `YangMills.KP.summable_finset_pinnedClusterWeight`, and
  `YangMills.KP.tsum_finset_pinnedClusterWeight_le` package the finite-pin
  scalar-norm bookkeeping and `tsum` exchange used by off-region and RG
  cluster-tail estimates;
* `YangMills.RG.clusterSkeletonRemainderSum_tsum_le_of_local` proves the
  pre-metric quantitative skeleton-pinned bound from the same local window;
* `YangMills.RG.clusterSkeletonRemainderSum_tsum_le_metric_bound_of_local`
  then adds the modified-metric activity estimate.  If the tilted local
  activity sum satisfies the volume-uniform KP smallness window and the
  tilted, cardinality-weighted activity of every hole polymer is bounded by
  `A * q^(d_M+1)`, the full skeleton-pinned cluster remainder series is
  bounded by
  `t⁻¹ * A * (1 - (3^d)^2 * (q * 2^(3^d+1)))⁻¹`.
* `YangMills.RG.clusterSkeletonRemainderSum_tsum_le_metric_bound_of_raw_local_metric`
  is the source-facing variant: it derives the local KP window from a
  raw-support local sum of the same modified-metric majorant, without
  inferring raw-support smallness from skeleton-rooted summability.
* `YangMills.RG.holePolymerSystem_KPCriterion_volumeUniform_exp` names the
  `ρ = exp(t)` bridge from the source-shaped local window
  `Σ_{Y∋s} exp(t) * ‖z(Y)‖ * exp(|Y|)` to the scalar-tilted KP criterion,
  with matching convergence and norm-bound companions.

Together with `clusterSkeletonRemainderSum_tsum_le`,
`holePolymerSystem_KPCriterion_volumeUniform_scaled`,
`holePolymerSystem_KPCriterion_volumeUniform_exp`,
`holePolymerSystem_converges_volumeUniform_scaled`,
`holePolymerSystem_norm_clusterSum_le_volumeUniform_scaled`,
`holePolymerSystem_converges_volumeUniform_exp`,
`holePolymerSystem_norm_clusterSum_le_volumeUniform_exp`,
`clusterSkeletonRemainderSum_term_le_skeletonPinned`,
`clusterSkeletonRemainderSum_term_le_pinned`,
`clusterSkeletonRemainderSum_summable`, `clusterUnionPolymer`, and
`clusterUnion_skeleton_card_le_clusterModifiedMetric_add_one`, this gives a
source-shaped cluster object, skeleton-pinned summability, and the
modified-metric consumer step that later `hRpoly` activity-decay work must feed.

## Live Frontier

The remaining hard input is still **not** a compiler trick:

* `hRpoly`: the concrete Yang-Mills single-scale activity-decay bound, i.e. the
  Dimock/Balaban cluster expansion with holes plus the fluctuation-integral
  estimate for the actual gauge RG operator.

The immediate P3 design constraint is now source-pinned: Dimock Appendix F
clusters use `Ω`-connectedness (`X₁ ∩ X₂ ∩ Ω ≠ ∅`), while the existing
`holePolymerSystem` uses full-polymer overlap/touching.  The Ω-active system
now has its own local KP criterion and cluster-sum consumers, so future
Appendix-F formalization can feed the source-facing relation directly.  The
touching-system local-KP consumers remain valid only for their stronger
hard-core system unless a comparison theorem is proved.

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
The character-level corollaries are also packaged:
`integral_character_mul_star_eq_zero_of_not_equiv` proves orthogonality of
inequivalent irreducible characters, and `integral_character_mul_star` proves
that an irreducible character has Haar `L²` norm one. The same facts are now
available directly through the Hilbert-space wrappers
`inner_characterL2_eq_zero_of_not_equiv` and `inner_characterL2`; finite
pairwise-inequivalent families are packaged as `orthonormal_characterL2`, and
`linearIndependent_characterL2` exposes the resulting finite linear
independence statement. The finite coefficient-extraction identity
`inner_characterL2_sum` recovers expansion coefficients by Haar `L²` inner
product inside such finite orthonormal character families, and
`characterL2_sum_eq_sum_iff` packages uniqueness of finite character expansion
coefficients in the same fixed family. Its zero-expansion consumer
`characterL2_sum_eq_zero_iff` gives the common "all coefficients vanish" form,
and `inner_characterL2_sum_sum` gives the finite diagonal Gram/Plancherel
identity for two such expansions. The norm-square corollary
`norm_sq_characterL2_sum` gives the corresponding finite Parseval identity,
and `norm_sq_characterL2_sum_sub_sum` gives the finite distance formula between
two coefficient vectors and their character expansions.

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
