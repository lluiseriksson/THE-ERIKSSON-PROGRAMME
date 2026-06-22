# Current State

**Verified public baseline for this live-state snapshot:** 2026-06-22,
the local verified checkpoint recorded by this commit (pending public
fast-forward push to `origin/main`; see `git log` and
`docs/VERIFICATION-LEDGER.md` for the exact commit history).

This file is the short, live entry point. Historical plans and ledgers are kept
because they matter, but this page is the first place a new reader should look
before deciding what is actually proved and what remains open.

Adversarial source-claim status, contradicted attributions, provenance fields,
and the remaining Balaban extraction queue are tracked separately in
[`docs/SOURCE-CLAIM-AUDIT.md`](docs/SOURCE-CLAIM-AUDIT.md).

## Verified Core

* `lake build YangMillsCore` is green at **8339 jobs**.
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
  `ℓ²`/`PiLp 2` spaces with the rescaling scalar left explicit.  The same
  averaging layer now exposes named finite stencils `fineLineSupport` and
  `linAvgSupport`, together with
  `linAvg_congr_of_eqOn_support` and
  `scaledLinAvgCLM_congr_of_eqOn_support`, so later kernel/locality work can
  consume finite support of `Q` without hard-coding its block/line indices.
  The gauge-precision bookkeeping layer now proves
  `coercive_add_adjointMass_of_blockPoincare` and
  `coercive_add_qMassCLM_of_blockPoincare`: an explicit block
  Poincare/Hodge inequality plus positivity of the background form gives
  coercivity of `K + a Q†Q` with constant `min 1 a / C_P`.  The companion
  composition layer `YangMills/RG/GaugeFixedPrecision.lean` packages the
  intended precision form `Kslice + a Q†Q - Σ`, proves the generic summable
  operator-budget theorem, records the strictly positive residual constant
  when `∑' δ < min 1 a / C_P`, specializes the result to `qMassCLM`, and adds
  finite Schur-Catalan quadratic-form budget corollaries.  The exact
  finite-dimensional covariance bridge `YangMills/RG/CoerciveCovariance.lean`
  turns any strictly coercive finite-dimensional precision operator into the
  continuous linear inverse `covarianceOfIsCoerciveCLM`, proves `C ∘ K = id`
  and `K ∘ C = id`, establishes `‖C‖ ≤ c⁻¹`, and proves nonnegativity of the
  inverse quadratic form.  The assembly module
  `YangMills/RG/GaugeFixedCovariance.lean` composes those two layers, so the
  abstract precision `K0 + a Q†Q - Σ` now gets an exact inverse covariance from
  the block-Poincare and norm-budget hypotheses alone.  The full-periodic
  cochain layer `YangMills/RG/PhysicalGaugeCochains.lean` now fixes the
  physical positive-bond coordinate convention for `su(N)` coordinates,
  carries an explicit adjoint-action model, defines background-covariant
  `D0`/`D1`, the covariant divergence, `Q†Q` gauge-fixing mass, the background
  Hodge operator, and the flat block constraint through the existing `linAvg`.
  Its Hodge and gauge-fixing quadratic identities are now exposed in the
  `inner A (K A)` orientation consumed by the generic coercivity API, while
  the older symmetric orientation is retained for direct adjoint calculations.
  The trivial-background flat specialization also exposes both orientations of
  the exact Hodge quadratic identity as named theorems, so a future
  `flatGaugeHodgePoincare` source theorem can target the flat operator directly
  without unfolding the background definition.  It also names the flat harmonic
  kernel predicate `IsFlatHarmonicOneCochain` and proves both orientations of
  the exact zero-quadratic-form test
  `isFlatHarmonicOneCochain_iff_flatGaugeHodgeK0_inner_right_eq_zero` /
  `isFlatHarmonicOneCochain_iff_flatGaugeHodgeK0_inner_eq_zero`, reducing
  vanishing of the flat Hodge energy exactly to simultaneous flat curl and
  gauge-divergence zero.  The operator-kernel form
  `flatGaugeHodgeK0CLM_eq_zero_iff_isFlatHarmonicOneCochain` now records the
  same equivalence for `K₀ A = 0` itself.  The trivial-background curl is now
  exposed pointwise as `covariantD1CLM_trivial_apply`, and flat harmonic
  cochains satisfy the resulting plaquette curl equation via
  `isFlatHarmonicOneCochain_curl_apply_eq_zero`.  This is a prerequisite for
  reverse classification, not the classification.  The averaging layer now proves
  the exact direction-wise constant calculations `fineLineSum_constant` and
  `linAvg_constant`: a bond field constant in each direction averages to `L`
  times that directional value.  The flat physical block constraint now also
  carries a named positive-bond stencil `flatBlockConstraintSupport`, together
  with `flatBlockConstraintQCLM_congr_of_eqOn_support`, lifting the existing
  `linAvgSupport` locality theorem to the physical cochain API.  It also has
  direction-wise constant one-cochains `constantPhysicalGaugeOneCochain`, the
  exact formula `flatBlockConstraintQCLM_constant_apply`, and
  `flatBlockConstraintQCLM_injective_on_constants`, certifying that the block
  term removes the direction-constant sector at the finite-combinatorial
  level.  The same constant-sector audit now also proves
  `flatBlockConstraintQCLM_constant`, the zero flat-curl identity
  `covariantD1CLM_trivial_constantPhysicalGaugeOneCochain`, the finite
  periodic summation-by-parts identity
  `inner_constantPhysicalGaugeOneCochain_covariantD0CLM_trivial`, the zero
  flat gauge-divergence identity
  `gaugeConstraintQCLM_trivial_constantPhysicalGaugeOneCochain`, and
  `isFlatHarmonicOneCochain_constantPhysicalGaugeOneCochain`: every
  direction-wise constant one-cochain is a flat harmonic at the trivial
  background.  The audit also exposes
  `flatGaugeHodgeK0CLM_constantPhysicalGaugeOneCochain`, the corresponding
  operator-kernel statement for the flat Hodge operator, and
  `flatBlockConstraintQCLM_constant_eq_zero_iff`, the exact detection of
  zero constants by the block map.  The theorem
  `flatConstant_jointKernel_eq_zero_iff` packages these facts as the exact
  triviality of the joint flat-Hodge/block kernel on the direction-wise
  constant sector.  The constant-sector norm layer
  `YangMills/RG/PhysicalGaugeFlatPoincare.lean` now proves
  `norm_sq_constantPhysicalGaugeOneCochain`,
  `flatBlockConstraintQCLM_constant_norm_sq`, and
  `flatBlockConstraint_controls_constantSector`, including the exact
  normalization
  `‖const_{L*N'} v‖² = ((L : ℝ)^d / (L : ℝ)^2) ‖Q const_{L*N'} v‖²`
  for the current unscaled line-integral block map.  The reverse
  classification and the uniform full-periodic Poincare theorem remain
  unproved.  The
  full-periodic flat Hodge/block-Poincare interface is now isolated in
  `YangMills/RG/PhysicalGaugeHodgePoincare.lean`: the predicate
  `FlatGaugeHodgePoincare` states the exact physical-cochain estimate for
  `K₀ = D₁†D₁ + D₀D₀†` plus the separate block map
  `flatBlockConstraintQCLM`, and `flatGaugeHodgePoincare` repackages a
  source-supplied curl/divergence/block inequality into that operator form.
  The source inequality itself is not proved there.
  The finite physical interface `YangMills/RG/PhysicalGaugeOperator.lean`
  separately defines active regions with Dirichlet zero-extension/restriction
  maps, flat `d0`/`d1` operators with `d1 ∘ d0 = 0`, the flat gauge constraint,
  the PSD flat slice, a positive-bond block derivative wrapper, and the soft
  full-space precision shell `physicalKslice + a Q†Q`.  These layers remain
  pre-physical operator infrastructure: they do not construct the Yang--Mills
  Hessian, prove the physical decomposition equality, prove a source Poincare
  theorem, establish propagator decay, or construct a localized covariance root;
* gauge covariance of the averaged-contour interface;
* near-identity logarithm, small-field stability lemmas, and the local
  two-sided cutoff dictionary `norm_nearLog_two_sided_of_norm_le_third`,
  converting `‖Y‖ ≤ 1/3` into mutual control of `Y` and `nearLog Y` up to the
  constant `2` for the faithful variable `Y = D - 1`;
* explicit l2 contraction of `Q`;
* free Gaussian covariance pushforward, finite-dimensional Gaussian
  construction, and finite Gaussian block collars
  `gaussianBlockKernel` / `gaussianBlockTransform`, whose translated
  fluctuation kernel and product block transform are proved to remain
  probability measures before any interacting Appendix-F activity is inserted.
  The finite collar now also exposes the continuous linear block map
  `gaussianBlockCLM` and proves Gaussian closure:
  `gaussianBlockKernel_isGaussian` and
  `gaussianBlockTransform_isGaussian`;
* marginal-coupling summability and conditional UV mass-gap assembly;
* the explicit producer/consumer split for the UV scalar estimate:
  `RawYMActivityDecay`, `RenormalizedHoleActivityDecay`, and
  `SingleScaleUVDecay`, with
  `singleScaleUVDecay_of_renormalizedHoleActivities` bridging with-holes
  activities to the scalar bound consumed by `UVMassGap`;
* the residual Appendix-F with-holes bridge
  `YangMills/RG/PolymerClusterWithHolesBridge.lean`: it defines
  `polymerClusterResidualRate κ κ₀ = κ - 3κ₀ - 3`, proves that
  `κ ≥ 3κ₀ + 3` only gives nonnegative residual decay, proves the reusable
  summability margin `κ₀ ≤ κ - 3κ₀ - 3` from the stronger
  `κ ≥ 4κ₀ + 3`, and packages both the static aggregate
  `polymerClusterWithHoles_abs_tsum_le` and the producer bridge
  `singleScaleUVDecay_of_clusterWithHolesActivities`.  It now also instantiates
  the summability substrate over the concrete rooted, hole-respecting modified
  metric via `rooted_exp_discreteModifiedMetric_tsum_le` and
  `rooted_polymerClusterWithHoles_abs_tsum_le`, translating
  `exp (-κ₀(d_M+1))` into the existing `q^(d_M+1)` theorem with
  `q = exp (-κ₀)`.  It now also exposes the same rooted aggregate directly on
  the source-facing `OmegaPolymerType` via `omegaRootedPolymerEquiv`,
  `omega_rooted_exp_discreteModifiedMetric_tsum_le`, and
  `omega_rooted_polymerClusterWithHoles_abs_tsum_le`.  The same concrete
  rooted omega-pinned hypotheses now feed the scalar UV consumer through
  `singleScaleUVDecay_of_omegaRootedClusterWithHolesActivities`, with the
  explicit sufficient margin corollary
  `singleScaleUVDecay_of_omegaRootedClusterWithHolesActivities_four_mul_margin`;
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
  graph also have pairwise disjoint active supports inside Ω.  The canonical
  `confinedComponentCoverFamily` indexed by the confined components has cover
  indices whose union is exactly the original finite cover set `K`, and these
  indices are pairwise disjoint for distinct family entries.  The support
  bridge
  `LocalActivity.mayerCoverActivity_integral_factor_confinedOmegaComponents_of_fluctuationSupport_subset`
  states the exact finite hypothesis under which these Ω-components factorize
  the ultralocal fluctuation integral: every fluctuation support must lie inside
  its declared Ω-active support.  The graph-level adapter
  `LocalActivity.fluctuationOverlapGraph_adj_imp_omegaOverlapGraph_adj_of_fluctuationSupport_subset`
  isolates the edge implication used by that bridge: under the same support
  containment, every actual fluctuation-overlap edge is an Ω-overlap edge.
  The companion
  `OmegaConnectedCover.mayerActivity_integral_factor_confinedComponentCoverFamily_of_fluctuationSupport_subset`
  exposes the same factorization directly as a product over the canonical
  `confinedComponentCoverFamily`;
* the finite Appendix-F target compiler
  `YangMills/RG/AppendixFFiniteCover.lean` now closes the single-support
  target-family Fubini/lumping identity: target choices are reindexed by
  admissible connected-cover families, the connected-cover family sum equals
  the product over target fiber activities `K(Y)`, and the exact finite target
  hard-core partition is identified with the raw Mayer product.  The headline
  theorems are
  `sum_appendixFAdmissibleTargetChoices_eq_sum_admissibleConnectedCoverFamilies`,
  `sum_admissibleTargetFamilies_prod_connectedMayerActivity_eq_sum_admissibleConnectedCoverFamilies`,
  `prod_one_add_eq_appendixFTargetPolymerSystem_partition`, and
  `complex_exp_sum_eq_appendixFTargetPolymerSystem_partition`.  This remains
  finite algebra for the case where the same support map controls
  connectivity and target unions; the concrete with-holes two-support closure
  lives in the next two modules;
* the source-faithful two-support holes geometry bridge
  `YangMills/RG/AppendixFHoleTarget.lean`: for `omegaHolePolymerSystem`, it
  proves `skeleton (⋃ full targets) = ⋃ skeletons`, nonemptiness of full
  targets and target skeletons, connectedness and hole-respect of representable
  full targets, a coercion back to `OmegaPolymerType`, and
  injectivity/cardinality preservation of the full-target union map on
  admissible connected-cover families whose disjointness is only
  active-skeleton disjointness;
* the source-faithful two-support Appendix-F target-family compiler
  `YangMills/RG/AppendixFHoleTargetFamily.lean`: using active skeletons for
  admissibility and full unions for target fibers, it reindexes admissible
  target choices by connected-cover families and proves the finite raw Mayer
  product identity.  The headline theorems are
  `sum_appendixFHoleAdmissibleTargetChoices_eq_sum_admissibleConnectedCoverFamilies`,
  `sum_appendixFHoleAdmissibleTargetFamilies_prod_connectedMayerActivity_eq_sum_admissibleConnectedCoverFamilies`,
  `prod_one_add_eq_sum_appendixFHoleAdmissibleTargetFamilies`, and
  `complex_exp_sum_eq_sum_appendixFHoleAdmissibleTargetFamilies`.  This is
  still exact finite combinatorics, not the metric estimate (641), activity
  bound (642), `K#` integration, second Ursell expansion, or Yang-Mills raw
  activity decay;
* the first integrated Appendix-F activity layer
  `YangMills/RG/AppendixFKsharp.lean`: the connected target-fiber scalar
  activity `K(Y)` is lifted to the type-local object
  `appendixFHoleConnectedLocalActivity`, whose global evaluation is exactly the
  existing scalar `appendixFHoleConnectedMayerActivity` applied to the
  pointwise raw Mayer factors.  The same checkpoint adds
  `LocalActivity.finsetSum`, `LocalActivity.integrateFluctuation`,
  `appendixFHoleKsharp`, and
  `norm_appendixFHoleKsharp_globalEval_le`, carrying an explicit
  `Integrable` hypothesis so later Appendix-F integration statements do not
  hide totalized integrals.  The same file now records the exact finite
  support-containment bridge: if each raw local activity has spectator and/or
  fluctuation support inside its full source polymer, then
  `appendixFHoleConnectedLocalActivity ... Y` has the corresponding support
  inside `Y`; after fluctuation integration, `appendixFHoleKsharp ... Y` has
  spectator support inside `Y`.  It now also proves the active-skeleton
  support form needed by admissible target families and uses the n-ary
  ultralocal product-measure factorization from
  `YangMills/RG/UltralocalFactorization.lean` to factor finite products of
  connected target activities into products of `K#(Y)` whenever raw
  one-polymer fluctuation supports lie inside their active skeletons.  The
  spectator analogue factors products of `K#(Y)` over admissible target
  families under a second ultralocal product measure.  The same finite
  identities are now summed over all admissible target families:
  `integral_sum_appendixFHoleConnectedLocalActivity_eq_sum_prod_Ksharp_of_local_fluctuationSupport_subset_skeleton`
  turns the finite connected-target partition sum into the finite `K#` target
  sum after fluctuation integration, and
  `integral_sum_appendixFHoleKsharp_eq_sum_prod_integral_of_admissibleTargetFamilies`
  integrates that finite `K#` target-family gas under a spectator product
  measure.  This is Dimock (643)--(644)'s finite support/factorization
  substrate only; it does not prove the source activity estimate, the second
  target gas, Ursell `H#`, metric estimate (642), or any concrete Yang-Mills
  raw activity producer;
* the finite quantitative first-activity layer
  `YangMills/RG/AppendixFQuantitative.lean`: a raw pointwise exponential
  bound `‖h X‖ ≤ H0 * exp(-κ * metric X)` with `0 ≤ H0 ≤ 1` and `0 ≤ κ`
  implies the connected-cover majorant
  `norm_appendixFConnectedActivity_le_metricCoverSum`, and the with-holes
  specialization
  `norm_appendixFHoleConnectedMayerActivity_expSubOne_le_metricCoverSum`.
  The same module now packages the finite metric weight/sum and proves the
  local pinned bridge
  `norm_appendixFHoleConnectedMayerActivity_expSubOne_le_pinnedMetricCoverSum`:
  if `r ∈ Y`, the target-fiber sum is dominated by the finite sum over all
  connected covers containing some raw full polymer through `r`.  This proves
  triangle/product-norm, finite localization, and now the finite with-holes
  modified-metric stitching
  `appendixFHoleTargetFiber_discreteModifiedMetric_add_one_le_sum`:
  for every skeleton-connected target fiber cover,
  `d_M(Y, mod holes)+1 ≤ Σ_X (d_M(X, mod holes)+1)`.  It also now records the
  overlap-safe full-cardinality cover budget
  `appendixFHoleCoverUnion_card_le_metricSum_of_source_card_le_metric` and its
  target-fiber form
  `appendixFHoleTargetFiber_card_le_metricSum_of_source_card_le_metric`: if
  every source polymer in the selected cover satisfies
  `|X| <= theta * (d_M(X)+1)`, then the represented full target satisfies
  `|Y| <= theta * Σ_X (d_M(X)+1)`.  This is intentionally a cover-sum bound,
  not a replacement for the still-missing direct source/geometric compression
  `|Y| <= theta * (d_M(Y)+1)`.  The right-hand side of
  the first-activity estimate is still a finite connected-cover sum, so no
  connected-cover entropy estimate, activity bound (642), ultralocal
  integration to `K#`, second Ursell expansion to `H#`, or Yang-Mills raw
  activity estimate is hidden here;
* the finite target-fiber entropy layer
  `YangMills/RG/AppendixFFiberEntropy.lean`: the target-fiber
  overcounting step is now theorem-fed.  It proves skeleton monotonicity,
  the inclusion of a target fiber into the nonempty powerset of raw indices
  whose full target support lies in `Y`, and
  `appendixFTargetFiber_prod_le_exp_sub_one`, which bounds the nonnegative
  fiber product sum by
  `exp (sum_{X subset Y} w X) - 1`.  This is exactly the finite
  "forget connectivity and exact union, then exponentiate" step needed before
  the local modified-metric summability estimate.  It still does not prove
  the closed Dimock (642) activity bound, the `B0` local summability adapter,
  ultralocal integration/factorization to `K#`, the second Ursell expansion
  to `H#`, or any concrete Yang-Mills raw activity decay;
* the local Appendix-F summability adapter
  `YangMills/RG/AppendixFLocalSummability.lean`: it defines the shifted
  weight `appendixFHoleExpWeight HF κ X = exp(-κ(d_M(X)+1))` and the
  first-gas rate `appendixFKsharpRate κ κ₀ = κ - κ₀ - 2`.  It proves
  `appendixFKsharpRate_sub_left`, the algebraic identity needed to preserve
  the canonical rate definition while exposing a shifted source rate
  `appendixFKsharpRate (κ - θ) κ₀ =
  appendixFKsharpRate κ κ₀ - θ`, and
  `appendixFHole_rootedFiniteExpWeightSum_le`, restricting the concrete
  rooted omega modified-metric summability theorem to any finite raw family
  `Λ`, and
  `appendixFHole_containedWeightSum_le_metric_mul_of_rooted`, converting
  rooted local control into a target-contained estimate by overcounting
  through roots in `skeleton HF Y` and using
  `skeleton_card_le_discreteModifiedMetric_add_one`.  This is finite
  summability bookkeeping before the first-activity estimate, not the second
  gas;
* the source-shaped first `K#` estimate
  `YangMills/RG/AppendixFKsharpEstimate.lean`: it proves the exact pointwise
  exponential-minus-one bound
  `norm_appendixFHoleConnectedLocalActivity_globalEval_le_expSubOne` by
  combining raw metric decay, finite target-fiber entropy, modified-metric
  stitching, and target-contained local summability.  It then transfers the
  same bound to the integrated first activity through
  `norm_appendixFHoleKsharp_globalEval_le_expSubOne_of_rawMetricDecay`, with
  integrability still explicit, and provides the rooted-summability consumer
  `norm_appendixFHoleKsharp_globalEval_le_expSubOne_of_rawMetricDecay_rooted`.
  The output is the exact nonlinear factor
  `exp(2 H₀ K₀ (d_M(Y)+1)) - 1`.  It now also includes the finite cover-level
  target-cardinality tilt
  `appendixFHoleMetricCoverWeight_mul_exp_card_le_shifted_of_source_card_le_metric`:
  from a source budget `|X| <= theta * (d_M(X)+1)` on `Λ`, every target-fiber
  cover absorbs `exp |Y|` by shifting the cover rate from `κ` to `κ - θ`.
  This is still a cover-sum statement, not a direct target-metric compression.
  The linearized `κ - κ₀ - 2` corollary, Dimock (643) factorization, second
  Ursell gas, final `H#` residual rate, and concrete Yang-Mills raw activity
  estimate remain open;
* the second Appendix-F hard-core gas layer
  `YangMills/RG/AppendixFSecondGas.lean`: it defines the evaluated scalar
  activity
  `appendixFHoleSecondGasActivity HF z Λ Hraw μ ψ Y =
  (appendixFHoleKsharp HF z Λ Hraw μ Y).globalEval ψ` and instantiates it as
  `appendixFHoleSecondGas` through the existing source-facing
  `omegaHolePolymerSystem`.  The projection theorem
  `appendixFHoleSecondGas_activity` identifies the gas activity with `K#`,
  while `appendixFHoleSecondGasActivity_eq_zero_of_not_mem_targetRegion`
  proves the zero extension outside representable first connected-cover
  targets.  The KP interface is deliberately honest:
  `AppendixFHoleSecondGasKPMajorant` includes the exact tilt/cardinality
  factors required by the current KP theorem, and
  `appendixFHoleSecondGas_KPCriterion_of_majorant` applies the existing
  `omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp_of_metric_bound`.
  The same module now records the spectator-integrated scalar normal form
  `appendixFHoleIntegratedKsharpActivity HF z Λ Hraw μ ν Y =
  ∫ ψ, (appendixFHoleKsharp HF z Λ Hraw μ Y).globalEval ψ dν`, the
  corresponding scalar hard-core gas `appendixFHoleIntegratedSecondGas`, the
  zero-extension theorem outside the first target region, the integrated
  scalar KP interface
  `AppendixFHoleIntegratedSecondGasKPMajorant` /
  `appendixFHoleIntegratedSecondGasKPMajorant_of_norm_bound` /
  `appendixFHoleIntegratedSecondGas_KPCriterion_of_majorant`, and the finite
  normalization identity
  `integral_sum_appendixFHoleKsharp_eq_sum_prod_integratedKsharpActivity_of_admissibleTargetFamilies`,
  which rewrites the integrated finite `K#` target-family gas as a finite
  target-family sum using this scalar `z_K` activity.  The CMP116 adapter
  exposes the same integrated scalar KP entry point as
  `BalabanCMP116AppendixFIntegratedSecondGasKPMajorant` and
  `balabanCMP116AppendixFIntegratedSecondGas_KPCriterion_of_majorant`, and
  now composes the source-measurable rooted raw-metric `K#` estimate into that
  majorant through
  `BalabanCMP116AppendixFIntegratedSecondGasKPMajorant_of_rawMetricDecay_rooted_of_source`
  once the remaining scalar KP profile inequality is supplied.  The scalar
  profile has also been split into a reusable exponential absorption lemma,
  `appendixFHoleExpWeight_tilted_profile_le_of_card_le_metric`, and the CMP116
  wrappers
  `BalabanCMP116AppendixFIntegratedSecondGasKPMajorant_of_rawMetricDecay_rooted_of_source_of_card_le_metric`
  and
  `balabanCMP116AppendixFIntegratedSecondGas_KPCriterion_of_rawMetricDecay_rooted_of_source_of_card_le_metric`.
  These reduce the profile to an explicit full-cardinality budget
  `|Y| <= theta * (d_M(Y)+1)` plus the choice
  `q = exp (-(appendixFKsharpRate kappa kappa0 - theta))`.  The full-cardinality
  budget is not automatic from the skeleton metric; the newly verified finite
  target-fiber budget only gives the weaker cover-sum form
  `|Y| <= theta * Σ_X (d_M(X)+1)` from source polymer cardinality estimates.
  Closing the direct target-metric budget remains a source/geometric obligation.
  This does not prove Dimock (642), the conversion from the exact nonlinear
  `K#` estimate to the KP-ready majorant, any concrete integrability/source
  estimate for the integrated scalar activity, the second Ursell `H#`
  estimate, or any residual decay theorem;
* the second Ursell object layer
  `YangMills/RG/AppendixFHsharp.lean`: it defines the fixed-size
  union-fiber contribution `appendixFHoleHsharpTerm`, the totalized
  `appendixFHoleHsharp = tsum_n appendixFHoleHsharpTerm`, and the actual
  evaluated `K#` specialization `appendixFHoleHsharpOfKsharp`, together with
  the spectator-integrated scalar specialization
  `appendixFHoleHsharpOfIntegratedKsharp`.  The finite theorem
  `appendixFHoleHsharpTerm_eq_sum_filter` rewrites each term as a sum over
  the exact fiber of tuples whose `omegaClusterUnion` is the target `Y`;
  `appendixFHoleHsharpTerm_eq_zero_of_no_union` records the zero-fiber case;
  and `sum_appendixFHoleHsharpTerm_eq_clusterSum_term` proves that summing
  fixed-size fiber terms over all targets recovers exactly the fixed-size
  term of the KP `clusterSum` of the second gas.  This is finite bookkeeping
  only: it does not justify exchanging the finite target sum with the outer
  `tsum`, prove convergence, identify a partition logarithm, prove the
  residual decay rate, or extract a real scalar remainder;
* the residual second-Ursell adapter
  `YangMills/RG/AppendixFHsharpResidual.lean`: it converts a source-supplied
  complex-norm estimate for `appendixFHoleHsharp` at residual rate
  `κ - 3κ₀ - 3` into the real-valued `ClusterWithHolesActivityDecay`
  predicate for any explicitly contractive real extraction
  `|toReal w| <= ‖w‖`.  Its rooted theorem then feeds the existing concrete
  omega-rooted modified-metric summability bridge and obtains
  `SingleScaleUVDecay` for the scalar remainder
  `Rsc t k = ∑' P, toReal (appendixFHoleHsharp ... P)`, either under the
  direct residual domination hypothesis `κ₀ <= κ - 3κ₀ - 3` or under the
  sufficient margin `κ >= 4κ₀ + 3`.  This is only the adapter from a proved
  source residual estimate to the UV consumer; it does not prove the source
  `H#` estimate (Dimock F.1/(636)), convergence of the `H#` Ursell series,
  or the physical real
  projection.  The module now also names the canonical contractions
  `complex_re_contracts_norm` and `complex_im_contracts_norm`, and specializes
  the producer to real and imaginary parts through
  `singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re`,
  `singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin`,
  `singleScaleUVDecay_of_omegaRootedAppendixFHsharp_im`, and
  `singleScaleUVDecay_of_omegaRootedAppendixFHsharp_im_four_mul_margin`.
  The real-part theorem is the current concrete scalar adapter; a later
  physically normalized projection still needs its own definition and
  contraction proof if it differs from `Complex.re`;
* the finite partial second-Ursell layer
  `YangMills/RG/AppendixFHsharpPartial.lean`: it defines
  `appendixFHoleHsharpPartial HF zK N Y` as the finite sum of
  `appendixFHoleHsharpTerm` over cluster sizes `< N`.  The theorems
  `appendixFHoleHsharpPartial_zero` and
  `appendixFHoleHsharpPartial_succ` give the truncation recursion, while
  `sum_appendixFHoleHsharpPartial_eq_sum_clusterSum_terms` proves that
  summing the finite partial object over all target unions equals the finite
  sum of the corresponding ordinary KP cluster-sum terms.  The same module
  mirrors the residual adapter at finite cutoff via
  `clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharpPartial_le`,
  `rooted_clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharpPartial_le`,
  `singleScaleUVDecay_of_omegaRootedAppendixFHsharpPartial`, and real-part
  specializations with and without the margin `κ >= 4κ₀ + 3`.  This is
  convergence-free staging: it does not prove that the partial objects
  converge to `appendixFHoleHsharp`, nor any residual analytic estimate;
* the convergence interface for the second-Ursell layer
  `YangMills/RG/AppendixFHsharpConvergence.lean`: it proves that fixed-target
  summability of the `appendixFHoleHsharpTerm` sequence makes the finite
  truncations converge to the totalized `appendixFHoleHsharp`.  It now also
  exposes the exact decomposition
  `appendixFHoleHsharp = appendixFHoleHsharpPartial + tail`, proves that the
  truncation error tends to zero, and bounds the error norm by the shifted
  norm-tail sum.  Any residual complex-norm bound uniform over all finite
  partial cutoffs passes to the totalized `H#`.  The same module packages this
  limit passage into the total residual activity-decay and omega-rooted
  `SingleScaleUVDecay` producers, including the real-part specialization and
  the sufficient margin `κ >= 4κ₀ + 3`.  This is still a contract interface:
  it does not prove the fixed-target summability, quantitative tail decay, the
  uniform finite-partial residual bound, the source `H#` estimate
  (Dimock F.1/(636)), or any continuum/Clay theorem;
* the pointwise limit-transfer interface
  `YangMills/RG/AppendixFHsharpLimit.lean`: it separates explicit convergence
  of finite `H#` partials from the analytic proof of that convergence.  A
  pointwise limit hypothesis plus a residual bound uniform in cutoff yields
  the same residual norm bound for the total `appendixFHoleHsharp`; fixed-target
  summability supplies that convergence as a corollary; and the real-part
  four-margin theorem feeds this pointwise total bound into the existing
  omega-rooted `SingleScaleUVDecay` consumer without passing limits through
  the rooted polymer `tsum`.  This does not prove the second-Ursell majorant,
  the source `H#` estimate (Dimock F.1/(636)), the preceding `K/K#` estimate
  (Dimock (642)), or any continuum/Clay theorem;
* the termwise second-Ursell majorant interface
  `YangMills/RG/AppendixFHsharpMajorant.lean`: it proves that a summable
  real majorant for the norms of the fixed-target `appendixFHoleHsharpTerm`
  sequence supplies summability of the complex term sequence, finite partial
  norm bounds by finite majorant sums, shifted-tail bounds by shifted majorant
  sums, and a direct total `H#` residual bound when those finite majorant sums
  obey the residual profile.  It now also proves the finite exact-union
  bound `norm_appendixFHoleHsharpTerm_le_clusterWeight`: each target fiber is
  bounded by the global per-size KP `clusterWeight`, so the sharp
  `KP.KPCriterion` theorem gives fixed-target summability through
  `summable_appendixFHoleHsharpTerm_of_KPCriterion`.  The size-majorant
  residual consumers package the `tsum` residual-budget form needed by later
  source estimates, and the real-part omega-rooted four-margin theorem then
  feeds that termwise majorant contract into the existing UV consumer.  The
  global KP weight forgets the target `Y`, so this is not a target-sensitive
  residual decay estimate.  It does not prove the source majorant, the source
  `H#` estimate (Dimock F.1/(636)), the preceding `K/K#` estimate
  (Dimock (642)), or any continuum/Clay theorem;
* the closed-form geometric `H#` majorant interface
  `YangMills/RG/AppendixFHsharpGeometricMajorant.lean`: it specializes the
  termwise majorant contract to bounds of the form
  `‖appendixFHoleHsharpTerm ... n‖ <= A * q^n` with `0 <= A` and
  `0 <= q < 1`.  It proves summability of `A*q^n`, the closed total
  `A*(1-q)⁻¹`, finite partial bounds by that total, shifted-tail bounds by
  `A*q^N*(1-q)⁻¹`, and the corresponding total `H#` residual and real-part
  omega-rooted UV consumers.  This removes only geometric-series bookkeeping;
  it does not prove that the source second-Ursell/KP analysis supplies such
  an `A,q`, the source `H#` estimate (Dimock F.1/(636)), the preceding `K/K#`
  estimate (Dimock (642)), or any continuum/Clay theorem;
* the triple-infinity closure module
  `YangMills/RG/TripleInfinityClosure.lean`: it packages the marked-infinity
  bookkeeping suggested by the current notes.  A pointwise estimate
  `|H k n Y| <= M * eps k * (Lleaf * eps k)^n * w Y`, a uniform leaf budget
  `Lleaf * eps k <= q < 1`, a rooted target summability bound
  `sum w <= Kroot`, and a summable scale budget
  `eps k <= A * exp(-(c0*t)) * scaleWeight k`, `sum scaleWeight <= G0`,
  imply the iterated total influence bound
  `sum_k sum_n sum_Y |H k n Y| <=
   M*A*Kroot*G0*exp(-(c0*t))*(1-q)^(-1)`.  This is deterministic summation
  algebra over order, target, and scale; it does not prove the source activity
  estimate, the rooted geometry, the scale-coupling bound, or any physical
  Yang--Mills covariance statement;
* the source-facing absolute `H#` majorant bridge
  `YangMills/RG/AppendixFHsharpSourceMajorant.lean`: it defines the finite
  nonnegative fixed-union object `appendixFHoleHsharpAbsTerm`, proves the
  triangle-inequality bridge
  `norm_appendixFHoleHsharpTerm_le_absTerm`, and packages
  `AppendixFHsharpSourceMajorant` as the contract a future source proof should
  provide: amplitudes `A`, ratios `q`, `0 <= A`, `0 <= q < 1`, a termwise
  geometric bound, and the closed residual comparison.  It also supplies
  constructors from an absolute geometric estimate and from the preferred
  factorized shape
  `B(t,k) * exp(-r * (d_M(P)+1)) * rho(t,k)^n`, plus residual and UV
  adapters into the existing geometric consumers.  The namespace methods
  `summable_terms`, `tail_bound`, and `residual_bound` now expose the same
  convergence, truncation-tail, and pointwise residual consequences directly
  from a packaged source majorant.  It now also names the scale-indexed
  spectator-integrated first activity family
  `appendixFHoleIntegratedKsharpActivityFamily` and specializes the
  source-majorant constructors, residual estimate, and real-part omega-rooted
  UV consumer to the concrete normal form
  `appendixFHoleHsharpOfIntegratedKsharp`.  This proves only finite algebra
  and packaging; it does not prove the fixed-union absolute geometric source
  estimate, Dimock F.1/(636), Dimock (642), or any continuum/Clay theorem;
* the finite source-facing second-Ursell tree majorant
  `YangMills/RG/AppendixFSecondUrsellSource.lean`: it defines
  `appendixFHoleHsharpTreeTerm`, the exact fixed-union fiber with the same
  factorial normalization as `appendixFHoleHsharpAbsTerm` but with the absolute
  Ursell coefficient replaced by the finite sum over spanning trees of the
  tuple incompatibility graph.  The theorem
  `appendixFHoleHsharpAbsTerm_le_treeTerm` applies the already-proved Penrose
  tree-graph inequality coefficientwise.  The same module now supplies
  source-majorant constructors from tree-term geometric estimates, including
  the factorized modified-metric shape and the spectator-integrated `K#`
  specialization.  Thus the remaining finite source obligation is exposed as
  an estimate on `appendixFHoleHsharpTreeTerm` rather than on the more opaque
  absolute Ursell coefficient.  This is source-independent finite tree
  domination only; it does not prove Dimock's leaf summation, the `K#`
  estimate (642)/(644), the source `H#` estimate F.1/(636), the smallness
  condition, or any Yang-Mills raw activity bound;
* the source-facing geometric `H#` profile
  `YangMills/RG/AppendixFHsharpProfile.lean`: it packages the amplitudes
  `A`, ratios `q`, positivity/strict-ratio hypotheses, termwise `H#` bound,
  and closed-total residual comparison into one
  `AppendixFHsharpGeometricMajorantProfile` record.  The profile exposes
  `summable_terms`, `tail_bound`, `residual_bound`, and
  `singleScaleUVDecay_of_profile`, so a future KP/Ursell proof can feed the
  existing consumers with one object instead of repeating the same contract
  fields.  This is still packaging of the geometric-majorant obligation; it
  does not prove the source second-Ursell/KP estimate, Dimock F.1/(636),
  Dimock (642), or any continuum/Clay theorem;
* the residual with-holes `hpoly` bridge
  `YangMills/RG/PolymerClusterWithHolesBridge.lean`: once a residual
  pointwise bound
  `|H#(Y)| <= C H₀ exp (-(κ - 3κ₀ - 3) d(Y))` is supplied and the already
  available `κ₀`-weighted geometric summability holds, the bridge sums the
  activities to `C H₀ K₀` under the explicit condition
  `κ₀ <= κ - 3κ₀ - 3`.  Thus the source-side margin can be closed either by
  strengthening to `κ >= 4κ₀ + 3` or by proving geometric summability directly
  at the residual exponent.  This module is summation bookkeeping only: it does
  not prove the source `H#` estimate (Dimock F.1/(636)), the Yang-Mills raw
  activity estimate, or the
  continuum/OS reconstruction steps.  The module now includes the rooted
  concrete adapter
  `rooted_polymerClusterWithHoles_abs_tsum_le`, which uses
  `discreteModifiedMetric_weight_summable` directly and exposes the actual
  smallness condition
  `((3^d)^2) * (exp(-κ₀) * 2^(3^d+1)) < 1`.  The same bound is now available
  for the `OmegaPolymerType`/`omegaHolePolymerSystem` index shape through
  `omega_rooted_polymerClusterWithHoles_abs_tsum_le`, and a source-facing
  omega-rooted activity family can now be promoted directly to
  `SingleScaleUVDecay` by
  `singleScaleUVDecay_of_omegaRootedClusterWithHolesActivities`;
* the raw Mayer local transform `YangMills/RG/RawMayerWithHoles.lean`:
  `H ↦ exp H - 1` on `LocalFunctional` and `LocalActivity`, support
  preservation, off-support invariance, and the elementary small-activity bound
  `‖exp z - 1‖ ≤ 2‖z‖` for `‖z‖ ≤ 1`;
* the Ω-connected Mayer-cover substrate
  `YangMills/RG/OmegaConnectedCover.lean`: Ω-overlap graph on cover indices,
  `OmegaConnectedCover`, and the finite product
  `∏ᵢ (exp Hᵢ - 1)` as a type-local `LocalActivity` whose spectator and
  fluctuation supports are the corresponding unions.  The same file now lifts
  factorwise support containment into `Ω ∩ activeSupport i` to support
  containment for the whole Mayer-cover product, both for raw index sets and
  for `OmegaConnectedCover`, and also proves the pointwise quantitative
  product bound `‖∏ᵢ (exp Hᵢ - 1)‖ ≤ ∏ᵢ 2 Aᵢ` from factorwise small raw
  activity bounds `‖Hᵢ‖ ≤ Aᵢ ≤ 1`, together with the uniform-amplitude
  size profile `‖∏ᵢ (exp Hᵢ - 1)‖ ≤ (2A)^{|I|}` and its decay corollary
  `≤ (2A)^n` whenever `n ≤ |I|` and `2A ≤ 1`;
* the abstract activity-limit bridge
  `activity_profile_bound_of_tendsto`: a metric/profile bound uniform in a
  regulator passes to the pointwise limiting activity.  The same module also
  contains the telescopic regulator bridge
  `activity_profile_bound_of_tendsto_telescope`: if the initial activity has
  amplitude `amp` and the profile-weighted increments have summable budget
  `S`, then the pointwise limit has amplitude `amp + S`;
* exponential-decay kernel calculus, Schur bounds, the scalar
  Schur-Catalan budget closure, PSD kernel interface, Gaussian MGF bounds,
  and the collar-separated cross-sum bound
  `expDecay_separated_finset_sum_le`: an `ExpDecay` covariance kernel pays
  `exp(-κ ε)` across a separated collar, the algebraic core needed by the
  Gaussian collar-factorization route inspired by Lluis Eriksson's
  `2512.0064v1` outlook.  The new
  `schurCatalan_coercive_of_finset_budget` theorem records the finite
  scalar principle that a base coercivity constant stays positive after
  subtracting multiscale defects whose Schur-Catalan budgets sum below the
  base; it is bookkeeping only and does not prove the gauge-fixed Hessian,
  Schur-complement, propagator, R-operation, or raw activity estimates needed
  for P4;
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
* the finite Berezin algebra seed `YangMills/SUSY/FiniteBerezin.lean`: the
  exterior algebra over the finite complex space `Fin n → ℂ` now has the
  canonical exterior basis `finiteExteriorBasis` and the top-coefficient
  functional `finiteBerezinTop`.  It proves that the functional is `1` on the
  top monomial, `0` on every non-top basis monomial, and kills constants in
  positive fermionic dimension.  It also contains the algebraic exact-Ward
  package `FiniteBerezinExactWard`, proving that a finite linear `Q` with
  `finiteBerezinTop (Q F) = 0` cancels in decompositions `H = Q B + R`.
  The same file now also defines the weighted functional
  `finiteBerezinWeighted n weight F = finiteBerezinTop n (weight * F)`,
  proves that unit weight recovers `finiteBerezinTop`, and packages
  `FiniteBerezinWeightedExactWard` with the corresponding exact cancellation
  theorem for weighted finite Berezin integrals.  The top-density seed
  `finiteBerezinTopWeight n a = 1 + a • topBasis` proves the first
  normalization facts: in positive fermionic dimension it integrates `1` to
  `a` and scalar constants to `a * z`.  The generator-level theorem
  `finiteExteriorBasis_singleton_mul_self` proves Grassmann nilpotence:
  every degree-one exterior basis generator squares to zero.  The same file now
  exposes the general basis-product rules
  `finiteExteriorBasis_mul_of_not_disjoint` and
  `finiteExteriorBasis_powersetCard_mul_of_disjoint`: repeated generators kill
  a product, while disjoint products carry Mathlib's explicit orientation sign.
  `finiteBerezinTop_powersetCard_mul_of_disjoint_top` then extracts that sign
  as the top coefficient whenever the disjoint union fills all generators.
  The weighted top-density calculus is now basis-explicit as well: the empty
  monomial integrates to the prescribed coefficient `a`, the top monomial
  integrates to `1` in positive dimension, and every nonempty non-top monomial
  integrates to `0`.  The same top-density weight is now promoted from
  basis cases to a global linear identity:
  `finiteBerezinWeighted n (finiteBerezinTopWeight n a) =
  finiteBerezinTop n + a • finiteBerezinEmptyCoeff n` in positive fermionic
  dimension, so later finite Gaussian/Pfaffian expansions can consume the
  top and empty coefficients directly.  The product-facing companions now
  evaluate this same top-density on exterior-basis products: overlapping
  generator support gives zero, a disjoint product filling the positive top
  degree gives Mathlib's explicit exterior orientation sign, and disjoint
  nonempty non-top products give zero.
  The finite-sum layer now lifts these basis facts to explicit coefficient
  extraction on finite basis expansions: `finiteBerezinTop` selects the top
  coefficient, `finiteBerezinEmptyCoeff` selects the empty coefficient, the
  top-density weight sees exactly those two coefficients, and
  `finiteBerezinWeighted_sum_basis_mul_sum_basis` expands the weighted integral
  of two finite basis sums into the double sum of monomial products.  The
  filtered companion
  `finiteBerezinWeighted_sum_basis_mul_sum_basis_filter_disjoint` removes every
  repeated-generator pair from that double sum before later sign/top-degree
  monomial rules are applied.
  This is only the algebraic Berezin/Ward coefficient layer, not yet a
  super-Gaussian determinant/Pfaffian theorem.
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

The Appendix-F second-Ursell source path now also has a weighted finite tree
transfer layer.  `YangMills/RG/AppendixFSecondUrsellWeightedTree.lean` defines
`appendixFHoleHsharpWeightedTreeTerm`, proves its nonnegativity and the
order-zero normalization, and proves
`appendixFHoleHsharpTreeTerm_le_scaled_weightedTreeTerm`: a pointwise activity
bound `||zK Q|| <= epsilon * w Q` extracts the exact scalar
`epsilon^(n+1)` from the finite tree term.  The remaining missing theorem is
the source/geometry leaf summation bounding the weighted tree term itself.
The same module also now includes the finite factorized consumers
`appendixFHoleHsharpTreeTerm_le_factorized_of_weighted_bound` and
`appendixFHoleHsharpTreeTerm_le_factorized_of_weighted_geometric`, which turn
a weighted estimate `Croot * decay * Cleaf^n` into the preferred
`(Croot * epsilon * decay) * (Cleaf * epsilon)^n` tree-term shape.
`BalabanCMP116HsharpSource.lean` now exposes the corresponding CMP116
weighted-tree entry points:
`balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_weighted_tree_geometric`,
`balabanCMP116AppendixFHsharpCluster3Contract_of_weighted_tree_geometric`, and
`singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_weighted_tree_geometric`.
They take the weighted leaf estimate, the first-activity bound, and the
closed `(Croot * epsilon)/(1 - Cleaf * epsilon)` comparison as explicit
hypotheses, then feed the existing profile/cluster3/UV consumer stack.
The later source-facing endpoint
`singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_rawMetricDecay_rooted_canonicalRoot_halfBudget_of_sourceMeasurable`
packages the current raw-metric-decay, canonical-root, spectator-probability,
and source-measurability inputs in the shape now requested from the source
side.
The current CMP116 support package also supplies both finite hard-core graph
directions consumed by factorization bookkeeping: CMP116 Ω-overlap edges map to
Appendix-F skeleton-overlap edges, and skeleton-disjoint source polymers have
`F.zeta X Y = 1` and no CMP116 Ω-overlap edge.  These are consequences of the
single support hypothesis `F.activeSupport X subset skeleton HF X.val`; they do
not prove that CMP116 localization satisfies that hypothesis.
The scalar second-gas CMP116 layer also has the same KP-ready interface after
spectator integration:
`balabanCMP116AppendixFIntegratedSecondGas_KPCriterion_of_majorant` applies the
with-holes KP criterion to `balabanCMP116AppendixFIntegratedSecondGas` whenever
the explicit integrated scalar majorant, geometry, and smallness hypotheses are
supplied.  The source-package helper
`BalabanCMP116AppendixFIntegratedSecondGasKPMajorant_of_rawMetricDecay_rooted_of_source`
discharges the integrated scalar activity norm bound from `hraw`,
source-measurability, probability normalization, and the first-gas rooted
summability inputs; it still deliberately leaves the final tilted
`A,q` scalar profile as an explicit hypothesis.  The profile-calculus endpoint
`balabanCMP116AppendixFIntegratedSecondGas_KPCriterion_of_rawMetricDecay_rooted_of_source_of_card_le_metric`
discharges this scalar profile when a source/geometric theorem controls the
full target cardinality by `theta * (d_M+1)` and the constants are chosen with
`q = exp (-(appendixFKsharpRate kappa kappa0 - theta))`.
The source audit in `docs/CMP116-WEIGHTED-HSHARP-SOURCE-MAP.md` records the
current attribution boundary: CMP116 supports the product-Gaussian change of
variables, localized `H(Z)`, component factorization, hard-core `zeta`, and
Lemma 3/(2.38) decay estimate.  It does not yet supply the exact Lean support
theorem `F.activeSupport X subset X.val inter F.Omega` or
`F.activeSupport X subset skeleton HF X.val`; the printed phrase that `H(Z)`
is localized in the interior of `Z` still needs a source-to-Lean translation
with the enlargement, holes/large-field compatibility, metric convention, and
measurability/integrability hypotheses made explicit.  Dimock I Appendix B
supplies the no-hole leaf-summation mechanism, and Dimock II Appendix F
supplies the hole-aware final theorem, but the exact weighted order-wise `H#`
tree estimate remains unproved in the repository.

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

The P4 gauge-operator route now has a reusable coercivity-budget brick:
`YangMills.RG.CoercivePerturbation` defines `IsCoerciveCLM` and proves
stability of coercivity under additive/subtractive operator-norm perturbations,
including a summable family theorem
`isCoercive_sub_tsum_of_norm_budget`.  It is intentionally pre-physical: it
does not define the gauge-fixed Hessian, covariance, covariance root,
localization expansion, or CMP116 raw activity.  The next real P4 theorem is
still the source-backed construction/coercivity of the gauge-fixed precision
operator, with the perturbation budget supplied from the actual small-field
background formula.

On the Appendix-F/H# side, the raw-metric rooted leaf-summation endpoint now
also has the intermediate half-budget wrapper
`singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_rawMetricDecay_rooted_leafSummation_of_halfBudget`.
It keeps the explicit rooted first-cover budget `K₀` and `hroot`, while
deriving `hsmall`, `hρ1`, and `hBclosed` from the already-verified
second-Ursell half-budget closure.  The stronger canonical-root/source
measurability endpoints remain the most reduced public consumers.

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
