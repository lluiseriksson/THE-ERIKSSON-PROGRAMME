# Current State

**Live-state snapshot updated:** 2026-06-24.  **Latest recorded verification
checkpoint:** see [`docs/VERIFICATION-LEDGER.md`](docs/VERIFICATION-LEDGER.md),
Addendum 360.

This file is the short, live entry point. Historical plans and ledgers are kept
because they matter, but this page is the first place a new reader should look
before deciding what is actually proved and what remains open.

Adversarial source-claim status, contradicted attributions, provenance fields,
and the remaining Balaban extraction queue are tracked separately in
[`docs/SOURCE-CLAIM-AUDIT.md`](docs/SOURCE-CLAIM-AUDIT.md).

## Human Progress Dashboard

These bars are reader-facing estimates, not theorem probabilities.  They are
meant to make the state easy to scan; the authoritative record is still Lean,
the axiom oracle, and the verification ledger.

| Track | Bar | Current reading |
|---|---:|---|
| Verified core integrity | `100% [##########]` | zero `sorry`, zero project axioms, standard Lean axioms only |
| Strong-coupling lattice package | `100% [##########]` | KP/Mayer, clustering, and Wilson-loop area laws are theorem-fed |
| IR side of M3 lattice gap | `100% [##########]` | no carried IR hypothesis remains |
| Conditional M3 assembly | `90% [#########.]` | the assembly is verified; the UV producer remains explicit |
| Appendix-F/H# bridge to UV consumer | `78% [########..]` | source-facing endpoints exist; source estimates remain to be proved |
| P4 physical-operator vertical slice | `68% [#######...]` | cochains, gauge-fixed covariance, fixed-volume flat Hodge/Poincare closure, flat physical precision/covariance adapters, source-facing covariance/root localization APIs, local-SPD precision/root frontier packaging, a local fluctuation-activity certificate, dictionary-instantiated CMP116 localized-family bridge, Appendix-F support packaging, dictionary-backed Gaussian/activity construction scaffolding, a canonical Gaussian pushforward integral consumer, and source-package accessors for that consumer are in Lean |
| Concrete `hRpoly` discharge | `40% [####......]` | the live mathematical frontier |
| Strict Clay result | `0% [..........]` | **~0% (<0.1%)**, unchanged |

The full human-readable progress board now lives directly in
[`README.md`](README.md#progress-dashboard), so it is visible on the repository
front page.

## Verified Core

* `lake build YangMillsCore` is green at **8361 jobs** in the latest recorded
  verification checkpoint.
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
  the block-Poincare and norm-budget hypotheses alone.  The physical adapter
  `YangMills/RG/PhysicalGaugeFixedPrecision.lean` now specializes the same
  strict coercivity theorem to the fixed-volume flat Hodge operator and flat
  block constraint, and also gives the exact finite-dimensional covariance,
  inverse identities, operator-norm bound, and PSD quadratic form for that
  fixed-volume shell.  The companion localization interface
  `YangMills/RG/PhysicalGaugeCovarianceLocalization.lean` adds single-bond
  source cochains, kernel/finite-range/exponential covariance-localization
  predicates, and a certificate bundling the exact flat covariance with a
  supplied source-facing kernel bound.  The single-bond source is now identified
  with the `PiLp` singleton, has exact norm `‖v‖`, and every physical covariance
  operator gets the baseline constant kernel bound supplied by its operator
  norm.  It also adds a covariance-root
  certificate that consumes a localized covariance certificate while keeping
  the square-root identity, self-adjoint/PSD root structure, root norm bound,
  and root kernel localization as explicit source hypotheses.  The small
  perturbation budget, lack of volume-uniform constants, and actual covariance
  or covariance-root decay proof remain exposed.  The new source-facing
  activity layer `YangMills/RG/PhysicalGaugeFluctuationActivity.lean` packages
  local two-field physical gauge activities over positive bonds, active-support
  containment, raw pointwise bounds, and decay majorants around a supplied
  covariance-root certificate; the Hessian expansion, change of variables, and
  raw activity estimate remain source hypotheses.  The certificate now exposes
  named projection theorems for the raw bound, spectator/fluctuation supports,
  amplitude/weight nonnegativity, the separate decay majorant, and the combined
  raw-decay estimate.  The combined statement now also has the named predicate
  `PhysicalGaugeRawActivityDecay`, so future Appendix-F adapters can depend on
  stable field names without asserting that the physical-to-CMP116 conversion
  has been constructed.
  The bridge `YangMills/RG/PhysicalGaugeCMP116ActivityAdapter.lean` now records
  the finite physical-to-cube adapter layer before the stronger transport
  package: a `bondToCube` map, spectator/fluctuation coordinate pulls,
  projected active support, and a reindexed cube-local activity with exact
  `globalEval` and image-support theorems.  The adapter can now be instantiated
  directly from a `PhysicalGaugeCMP116Dictionary`; the dictionary supplies the
  exact fluctuation pullback on each physical bond, and Lean rewrites
  `globalEval`, spectator support, fluctuation support, and active support
  back to the dictionary's physical-bond preimage.  It also records the explicit
  localized-family constructor
  `PhysicalGaugeCMP116ActivityAdapter.localizedFamilyOfDictionary`, which turns
  dictionary-instantiated physical local activities into a
  `BalabanCMP116LocalizedActivityFamily` once measurability, physical
  support-containment, and physical active-support Ω-locality are supplied.
  This is still a finite support/measurability gate, not a construction of the
  physical activity.  The same file records the explicit
  transport obligations from that physical certificate to a CMP116 localized
  activity family: source-faithful `globalEval` preservation, active-support
  containment in the Appendix-F skeleton, and domination of the physical weight
  by the Appendix-F exponential weight.  It proves the formal consequences
  `physicalGaugeCMP116SupportHypotheses_of_transport` and
  `balabanCMP116_hraw_of_physicalGaugeCMP116ActivityTransport`, converting such
  a transport package into the existing CMP116 support package and `hraw`
  hypothesis shape.  Ω-locality, strong measurability, Gaussian preservation,
  metric normalization, and the actual physical construction of the transport
  package remain open.
  The same bridge now names the universal first-activity CMP116 raw metric
  decay predicate `BalabanCMP116RawMetricDecay`, exposes the carried CMP116
  family as
  `BalabanCMP116LocalizedActivityFamily.of_physicalLocalizedGaussianActivityCertificate`,
  and factors the physical-to-CMP116 raw-decay transport through
  `balabanCMP116RawMetricDecay_of_physicalGaugeRawActivityDecay`.  The older
  `balabanCMP116_hraw_of_physicalGaugeCMP116ActivityTransport` theorem is now a
  compatibility specialization of that named predicate; it still does not
  construct the CMP116 family or prove the physical raw estimate.
  The single-scale K# layer now also has the transport-level consumer
  `norm_balabanCMP116AppendixFIntegratedKsharpActivity_le_ksharpRate_of_transport`.
  It projects both the localized family `T.family` and the Appendix-F `hraw`
  premise from a supplied `PhysicalGaugeCMP116ActivityTransport`, so that K#
  call site no longer needs independent `F` and `hraw` arguments.  Probability,
  target-region membership, rooted leaf budget, smallness, and rate-margin
  hypotheses remain explicit.
  The corrected constructive route now starts upstream of that conditional
  bridge: `YangMills/RG/LocalLinearOperator.lean` defines the exact finite
  support calculus for CMP116 fluctuation-field operators.  It provides the
  projection `cmp116FieldProjection`, the predicate
  `OperatorSupportedBetween`, and closure/evaluation lemmas for agreement,
  output vanishing, addition, finite sums, composition, and monotone support
  enlargement.  This is deliberately not a raw-decay theorem and does not
  construct a physical CMP116 activity family.
  The full-periodic
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
  same equivalence for `K₀ A = 0` itself.  The trivial-background curl and
  gauge constraint are now exposed pointwise as `covariantD1CLM_trivial_apply`
  and `gaugeConstraintQCLM_trivial_apply`, and flat harmonic cochains satisfy
  the resulting plaquette curl and backward-divergence equations via
  `isFlatHarmonicOneCochain_curl_apply_eq_zero` and
  `isFlatHarmonicOneCochain_divergence_apply_eq_zero`, with the short alias
  `isFlatHarmonicOneCochain_div_apply_eq_zero` for downstream adapters.
  The underlying periodic lattice layer now packages the reusable shift
  calculus `FinBox.shift_bijective`, `FinBox.shiftBack_bijective`,
  `FinBox.sum_shift`, `FinBox.sum_shiftBack`,
  `FinBox.shift_shiftBack_comm`, the iterated-shift coordinate lemmas, and
  `FinBox.eq_default_of_shift_invariant`.  These are prerequisites for
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
  for the current unscaled line-integral block map.  It now also proves
  `flatGaugeHodgePoincare_constantSector_lower_bound`, so any
  `FlatGaugeHodgePoincare` constant must be at least this constant-sector
  normalization on a nonzero direction-wise constant mode.  The same module
  now defines the conditional bridge `FlatHarmonicKernelClassified`.  The finite
  torus module `YangMills/RG/FiniteTorusCurlDiv.lean` now proves the direct
  Laplacian classification theorem `periodicCurlDivKernelClassified` from the
  ordered plaquette curl and backward-divergence stencils, using
  `sum_inner_torusBackwardDiff`,
  `sum_inner_torusLaplacian_eq_neg_sum_norm_sq`,
  `torusLaplacian_component_eq_forwardDiff_divergence`, and
  `eq_default_of_torusLaplacian_eq_zero`.  The physical adapter
  `flatHarmonicKernelClassified_of_curl_div` now feeds the unconditional
  theorem into `flatHarmonicKernelClassified` and
  `flatHarmonic_eq_constantPhysicalGaugeOneCochain`; the fixed-volume theorem
  `exists_flatGaugeHodgePoincare` follows without carrying an external
  classification hypothesis.  It also proves the
  exact classified-kernel characterizations
  `flatHarmonicKernel_eq_constantSector` and
  `flatGaugeHodgeKernel_eq_constantSector`, and combines the carried
  classification with the constant-sector block audit in
  `flatJointKernel_trivial_of_harmonicClassification`.  This is only a
  reduction interface.  It also proves the finite-dimensional compactness step
  `exists_sq_norm_le_sum_three_sq_of_jointKernel_trivial`, derives the
  fixed-volume theorem
  `exists_flatGaugeHodgeBlockPoincare_of_jointKernel_trivial`, and packages the
  classification-dependent consequences
  `flatGaugeHodgeBlockPoincare_of_harmonicClassification` and
  `flatCurlDivBlockPoincare_of_harmonicClassification`.  As a verified base
  case, it proves `finBox_one_eq_iterShift`,
  `constant_of_shift_invariant_finBox_one`, and
  `flatHarmonicKernelClassified_one`: in one dimension, the pointwise flat
  divergence equation classifies flat harmonic one-cochains as direction-wise
  constants.  Consequently `flatGaugeHodgeBlockPoincare_one` and
  `flatCurlDivBlockPoincare_one` give fixed-volume one-dimensional
  Hodge/block-Poincare statements without carrying an external classification
  hypothesis.  The resulting Poincare constants may depend on the fixed volume;
  the volume-uniform full-periodic Poincare theorem remains unproved.  The
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
  invariant under off-support changes, finite products supported on support
  unions, and `LocalActivity.reindex`, which transports a source local activity
  along a site map with supports definitionally given by finite images;
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
  targets.  The generic Appendix-F `K#` and evaluated second-gas layers now
  also expose full-target and active-skeleton agreement wrappers:
  `appendixFHoleKsharp_globalEval_eq_of_agreeOn`,
  `appendixFHoleKsharp_globalEval_eq_of_agreeOn_skeleton`,
  `appendixFHoleSecondGasActivity_eq_of_agreeOn`, and
  `appendixFHoleSecondGasActivity_eq_of_agreeOn_skeleton`.  The KP interface
  is deliberately honest:
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
  term of the KP `clusterSum` of the second gas.  The underlying cluster
  geometry now also names component-containment lemmas for both the older
  hard-core `clusterUnion` and the source-facing `omegaClusterUnion`, including
  declared-union and skeleton variants.  These are the finite geometric facts
  needed before any later local-dependence theorem for `H#` can reduce
  component activities to agreement on the target union.  The `H#` layer now
  consumes that geometry: fixed-size terms and the totalized `H#` are unchanged
  when the second-gas scalar activity agrees on all component polymers contained
  in the declared target, with parallel active-skeleton variants; the evaluated
  `K#` specialization also inherits full-target and skeleton spectator-field
  agreement wrappers.  The spectator-integrated `K#` specialization now also
  exposes the corresponding full-target and skeleton wrappers as scalar
  integrated-activity extensionality theorems; after both fields are integrated
  there is no remaining external field-agreement parameter.  This is finite bookkeeping
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
  `sum w <= Kroot`, and a nonnegative summable scale budget
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
not prove that CMP116 localization satisfies that hypothesis.  The same
CMP116 localized-activity package now also exposes support-only dependency
wrappers: each raw activity and each finite Mayer product depend only on the
declared active support union, while retaining the sharper fluctuation support
inside `Omega` or `Omega ∩ activeUnion`.
The CMP116 `K#` adapter now names the matching first-integration consequences:
the connected first activity and the integrated `K#` depend only on either the
full target `Y` or the active skeleton `skeleton HF Y`, whenever the existing
Appendix-F support hypotheses supply the corresponding support inclusion.
The evaluated CMP116 second-gas activity now carries the same two dependency
wrappers, so later scalar KP/factorization code can cite the second-gas layer
directly instead of unfolding through integrated `K#`.
The CMP116 `H#` adapter now also exposes the evaluated-`K#` normal form
`balabanCMP116AppendixFHsharpOfKsharp` and its full-target/skeleton
spectator-field dependency wrappers.  These are direct consumers of the
existing `BalabanCMP116AppendixFSupportHypotheses` package and the generic
Appendix-F `H#` locality theorems; they introduce no new localization or
measurability assumptions.
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
The source audit now also splits the post-product-Gaussian localization step as
row B5b in `docs/SOURCE-CLAIM-AUDIT.md`: CMP116 pages 13--14, equations
(2.7)--(2.10), expand `(C^(k))^(1/2)` using a resolvent/series route and
generalized random-walk expansions, then rewrite the product-Gaussian integral
as localized quantities `H(Z,Z0)` and `H(Z)`.  This is the primary source
anchor for the current `hrootPieces` activity-local agreement shape, while the
domain/enlargement translation and finite/infinite root-piece reconstruction
remain explicit source obligations.
The follow-on row B5c records the crucial design constraint from CMP116 pages
15--20, equations (2.14)--(2.38): Balaban estimates and resums the localized
activity `H(Z)` and proves Lemma 3's decay bound.  This does not provide an
exact finite root-piece reconstruction theorem for `(C^(k))^(1/2)`.  The next
Lean-facing source interface should therefore treat finite root-piece sums as
truncations or auxiliary approximations unless a separate exact
activity-support equality theorem is located.
Row B5d now records the next CMP116 step, PDF page 21 / equations
(2.39)--(2.41): Lemma 3's localized `H(Z)` bound is inserted into the
exponentiated polymer series to produce the effective-action bound (I.1.18)
after fixing the final `delta,L` normalization and the `C_3 epsilon_1`
smallness budget.  This is a consumer of the future `H(Z)` construction/decay
theorem, not covariance-root reconstruction.
The source-facing Lemma 3 output is now isolated in the activity-only module
`YangMills.RG.BalabanCMP116Lemma3Estimate`.  The canonical conclusion is the
Nat-source-metric proposition
`CMP116Lemma3ActivityEstimate physicalActivity sourceMetric blockScale C3
epsilon1 delta kappaSource`, with native exponential weight
`balabanCMP116Lemma3Weight`, raw-decay adapter
`balabanLemma3_rawActivityDecay`, and no `amplitude_nonneg` field.  The prior
real-distance helper `cmp116Lemma3Weight` remains only as a compatibility
weight alias; it is not the current Lemma 3 conclusion object.
The theorem-fed finite resummation interface remains in
`YangMills.RG.BalabanCMP116Lemma3`: `CMP116HResummation` names the four
pre-Lemma source summation families with dependent source-shaped indices
`D → P(D) → Z0(D,P) → Z0'(D,P,Z0)`, `balabanCMP116H` is their finite sum, and
`norm_balabanCMP116H_le_termWeightSum` proves the finite triangle-inequality
step from termwise summand estimates plus a pre-Lemma summed-weight budget.
The module targets the isolated Nat-source-metric estimate and still does not
derive those termwise/summed-weight inputs from CMP116 constants; that
extraction remains the active source task.
The first equation-level source interface for that extraction is now
`YangMills.RG.BalabanCMP116Eq229`.  It records the exact CMP116 (2.29) product
summability shape
`Σ_D Π_{Y∈D} α₆ exp(-δκ d_k(Y)) ≤ 1` and proves
`cmp116_DStage_sum_le_of_eq229`: if D-indexed terms are bounded by a
nonnegative base factor times the (2.29) product, then the D-sum is bounded by
that base factor.  This is only the first-stage finite resummation consumer; it
does not prove the small-`α₆`/large-`K` source assertion or any final Lemma 3
residual post-D budget.  It now also proves
`cmp116Eq229Product` and `cmp116Eq229Product_nonneg`, naming the fixed-`D`
product from Eq. (2.29) and its nonnegativity under `0 <= alpha6`.
The residual-stage layer then defines `cmp116Eq229WeightedPWeight` and proves
`cmp116PStageSummability_of_pResidualSummability_weighted`: a normalized
P-residual sum, multiplied by the Eq. (2.29) product, yields exactly the
budget-valued P-stage predicate with that same product as budget.  The
dependent lift
`cmp116PStageSummabilityScaleFamily_of_pResidualSummability_weighted` makes
this available over `(t, k)`.
The Eq. (2.29) module also retains
`CMP116PStageSummability`, a budget-valued fixed-`(Z,D)` P-stage predicate,
and `cmp116H_postDSum_le_of_pStage`, which combines that P-stage budget with
an explicit fixed-`P` nested `Z0/Z0'` residual estimate to recover the old
post-D `hpostD` inequality.  This helper does not identify the P-stage budget
with equation (2.30) or prove the remaining `Z0/Z0'` residual estimates.
The same file also proves
`cmp116H_termWeightSum_eq_nested`, the finite equality between the flattened
`cmp116HIndexFinset` term-weight sum and the nested
`D → P → Z0 → Z0'` sum, and `cmp116H_termWeightSum_le_of_eq229`, which uses
equation (2.29) to discharge the outer D-sum once a complete residual
`P/Z0/Z0'` bound is supplied.  The theorem
`cmp116Lemma3ActivityEstimate_of_eq229_postD` composes that derived budget with
the existing finite-resummation bridge, so callers can obtain the isolated
`CMP116Lemma3ActivityEstimate` from Eq. (2.29), the complex termwise estimate,
the activity-identification equality, and the explicit residual post-D bound,
without separately passing a monolithic `hbudget`.
The companion module `YangMills.RG.BalabanCMP116Lemma3ResidualStages` now
derives that residual post-D bound from three source-neutral normalized stage
predicates:
`CMP116PResidualSummability`, `CMP116Z0ResidualSummability`, and
`CMP116Z0PrimeResidualSummability`.  The theorem
`cmp116H_postD_sum_le_of_residualStages` proves the finite `P/Z0/Z0'`
resummation algebra from those predicates plus a pointwise factorization, and
`cmp116H_termWeightSum_le_of_eq229_of_residualStages` composes it with Eq.
(2.29).  These predicates are not assigned to CMP116 equation numbers here;
they remain explicit source obligations.
The P stage now has the source-shaped budget predicate
`CMP116PStageSourceBound` and the adapter
`cmp116PResidualSummability_of_pStageSourceBound`, which maps that bound plus
the explicit scalar restriction
`2 * (blockScale + 2)^4 * pEntropyConstant * epsilon2 * exp(5*kappa) <= 1`
to the normalized `CMP116PResidualSummability`.  This names the source-budget
shape without proving the construction of `pWeight`, the source constant
hierarchy, or the remaining `Z0/Z0'` stages.
The `Z0` stage now similarly has the source-shaped budget predicate
`CMP116Z0StageSourceBound` and adapter
`cmp116Z0ResidualSummability_of_z0StageSourceBound`, using the separate scalar
`(blockScale + 2)^4 * z0EntropyConstant * epsilon2 <= 1`.  This deliberately
omits the P-stage leading `2` and `exp(5*kappa)` factors, and uses a distinct
`z0EntropyConstant`; it still does not construct `Z0Index`, identify
`z0Weight`, prove the Z0 source estimate, or discharge the `Z0'` stage.
The same P-source package now feeds the normalized residual-stage consumers
through
`cmp116H_postD_sum_le_of_pStageSourceBound_residualStages`,
`cmp116H_termWeightSum_le_of_eq229_of_pStageSourceBound_residualStages`, and
`cmp116Lemma3ActivityEstimate_of_eq229_pStageSourceBound_residualStages`.
These wrappers only replace the `CMP116PResidualSummability` premise by the
source-shaped P bound plus its scalar smallness condition; Eq. (2.29),
`Z0/Z0'` residual summability, nonnegativity, pointwise factorization,
termwise estimates, and activity identification remain explicit hypotheses.
The same module now also exposes the source-order variant
`cmp116H_postP_sum_le_of_residualStages`, which turns normalized fixed-`P`
`Z0/Z0'` residual estimates into the post-`P` budget, plus
`cmp116H_postD_sum_le_of_pStageResidualStages`,
`cmp116H_termWeightSum_le_of_eq229_of_pStageResidualStages`, and
`cmp116Lemma3ActivityEstimate_of_eq229_pStageResidualStages`.  These compose
the newer budget-valued `CMP116PStageSummability` with the fixed-`P`
residual stages before applying Eq. (2.29), but still do not prove the
P-stage source budget, the `Z0/Z0'` residual estimates, or the source
constant hierarchy.
The module now also exposes the source-safe combined post-`P` route
`CMP116PostPResidualSourceBound`,
`cmp116PostPResidualBound_of_sourceBound`, `CMP116PostPResidualBound`,
`cmp116H_postD_sum_le_of_pStagePostPResidualBound`,
`cmp116H_termWeightSum_le_of_eq229_of_pStagePostPResidualBound`, and
`cmp116Lemma3ActivityEstimate_of_eq229_pStagePostPResidualBound`; the
scale-family wrapper
`cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStagePostPResidualBound`
applies the same route pointwise.  This is for source statements that control
the nested `Z0/Z0'` remainder together or in a different summation order.  It
does not identify a `Z0'` scalar, split the combined bound, prove source
estimates, or reduce the remaining activity/factorization obligations.
The compatibility theorem
`cmp116PostPResidualBound_of_residualStages` now records that the older split
normalized `Z0/Z0'` residual route is a special case of the combined
post-`P` predicate.  It is an interface bridge only: the split residual
estimates, product nonnegativity, and factorization remain explicit
hypotheses.  The source-bound adapter separately records that a supplied
post-`P` source amplitude/weight estimate implies the canonical consumer
bound only under an explicit majorization by the CMP116 Lemma-3 base factor.
The scale-family layer now also names the post-`P` route as a source-boundary
package:
`CMP116Lemma3PostPScaleSourceAssumptions` and
`CMP116Lemma3PostPScaleSourceAssumptions.lemma3_activity_estimate`.  This
packages Eq. (2.29), the P-stage budget, the direct combined post-`P`
residual bound, activity identification, and the complex termwise estimate
without introducing a standalone `Z0'` source scalar or a fixed-`Z0`
`Z0'` summability claim.
The admissible-domain adapter
`YangMills.RG.BalabanCMP116Lemma3AdmissibleAdapter` now records the honest
transport from CMP116's native admissible source domains to a larger repository
index type.  It defines the zero-extended metric
`cmp116AdmissibleMetricZeroExtension`, proves
`cmp116Lemma3ActivityEstimate_of_admissible_zeroExtension` and its scale-family
version from an explicit outside-domain zero theorem, composes the existing
post-`P` scale source package via
`CMP116Lemma3PostPScaleSourceAssumptions.lemma3_activity_estimate_admissible_zeroExtension`,
and adds
`balabanCMP116Lemma3Weight_domination_of_admissible_metricComparison`, which
requires both target-family admissibility and the full exponent comparison.
This proves no admissibility, no outside-zero construction, and no metric
comparison; it also proves none of the five post-`P` source fields carried by
`CMP116Lemma3PostPScaleSourceAssumptions`.
The raw-source compatibility bridge is downstream in
`YangMills.RG.BalabanCMP116Lemma3RawSourceAdapter`.  It contains the explicit
metric-domination theorem to `appendixFHoleExpWeight` and
`PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.of_lemma3ActivityEstimate`.
`BalabanCMP116SourceTheorem` again depends only on the raw-M3 source frontier
and keeps Lemma 3 activity packaging out of the five-field source theorem.
The module `YangMills.RG.BalabanCMP116Lemma3ScaleFamily` now adds the
dependent scale-family layer requested by the source split.  It packages
`∀ t k, CMP116Lemma3ActivityEstimate ...` over scale-dependent polymer types,
names the canonical per-scale Lemma 3 weight and amplitude, builds the
corresponding raw-source records through
`rawSource_of_lemma3ActivityEstimate`, and proves
`cmp116Lemma3ActivityEstimateScaleFamily_of_resummation` by applying the
single-scale finite resummation bridge at each `(t, k)`.  It also exposes
`cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_postD`, the pointwise
scale-family lift of the Eq. (2.29) post-D consumer.  This is downstream
packaging only: it does not derive the termwise estimates, residual post-D
budget, source metric comparison, Gaussian pushforward, covariance-root
localization, Wilson-Hessian identification, local physical activity
construction, or the rooted H# identity.
It now also exposes
`cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_residualStages`, which derives
the per-scale post-D budget from source-neutral `P/Z0/Z0'` residual-stage
predicates, a named `postDBase` equal to the Eq. (2.29) product-weight base,
and a pointwise residual factorization before applying the same activity
bridge.  The residual stage predicates remain unassigned source obligations.
It now also exposes
`cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStageResidualStages`, the
pointwise scale-family lift of the newer source-order route with explicit
`CMP116PStageSummability` and fixed-`P` `Z0/Z0'` residual-stage predicates.
This wrapper again proves no source inequality; it only applies the verified
single-scale finite-summation theorem at every `(t, k)`.
It now also exposes
`cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStageSourceBound_residualStages`,
which lifts the P-source-bound residual bridge pointwise in `(t, k)`.  This
wrapper replaces the per-scale normalized P residual premise by
`CMP116PStageSourceBound` plus the per-scale scalar smallness condition, while
keeping Eq. (2.29), `Z0/Z0'` residual summability, nonnegativity, factorization,
termwise estimates, and activity identification explicit.
The source-frontier file now also exposes the parallel record
`BalabanCMP116Lemma3SourceAssumptions`.  It keeps all existing covariance,
Gaussian, support, measurability, H#, marginal-flow, and IR assumptions
explicit, but replaces the arbitrary `raw_pointwise_decay` field by the
canonical `CMP116Lemma3ActivityEstimateScaleFamily`.  The direct constructor
`CMP116RawSourceM3Frontier.of_lemma3SourceAssumptions` projects that record to
the existing M3 frontier with canonical Lemma-3 weight/amplitude and derives
weight nonnegativity from the exponential weight theorem.
The same source-frontier file now also exposes
`BalabanCMP116Lemma3ResummationSourceAssumptions`.  This is a narrower
source-boundary record for the Lemma-3 lane: instead of assuming the whole
`CMP116Lemma3ActivityEstimateScaleFamily`, it carries the explicit Eq. (2.29),
`CMP116PStageSummability`, normalized fixed-`P` `Z0/Z0'` residual
summability, activity-identification, termwise-estimate, nonnegativity, and
pointwise factorization obligations already consumed by
`cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStageResidualStages`.
Its constructors derive the existing Lemma-3 source-assumption record and the
raw-source M3 frontier.  This is still only packaging of explicit obligations,
not a proof of the P-stage/residual source estimates or Lemma 3.
The raw-source M3 frontier namespace now also has the parallel constructor
`CMP116RawSourceM3Frontier.of_lemma3ResummationSourceAssumptions`, and
`BalabanCMP116Lemma3ResummationSourceAssumptions.to_m3Frontier` routes through
that constructor.  This is an API normalization only; the source obligations
and Clay distance are unchanged.

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

The P4 physical-operator route now has a deterministic vertical slice in
place.  `YangMills.RG.CoercivePerturbation` defines `IsCoerciveCLM` and proves
stability of coercivity under additive/subtractive operator-norm perturbations,
including `isCoercive_sub_tsum_of_norm_budget`.
`YangMills.RG.GaugeFixedPrecision` packages the intended
`Kslice + a Q†Q - Σ` precision form and proves coercivity under a summable
operator budget.  `YangMills.RG.CoerciveCovariance` then turns strict
finite-dimensional coercivity into an exact continuous linear inverse
`covarianceOfIsCoerciveCLM`, with both inverse identities and the norm bound
`‖C‖ ≤ c⁻¹`.  This is still intentionally pre-physical: it does not define the
actual Yang--Mills Hessian, prove the physical decomposition equality, prove
Combes--Thomas/propagator decay, construct a localized covariance root, or
produce the CMP116 raw activity.
`YangMills.RG.LocalSPDPrecision` now adds the first resolvent-first abstract
layer: finite-range small Neumann data are packaged as
`LocalFiniteRangeResolventData` and imply exponential decay of
`neumannResolventKernel`, while the inverse-square-root binomial coefficients
`choose(2n,n)/4^n` are bounded by one and have geometric shifted-tail bounds.
The same module now normalizes an abstract spectral sandwich `0 < m ≤ M` into
`q = 1 - m/M`, proves `0 ≤ q < 1`, records `1 - q = m/M`, and gives the
scaled `M^{-1/2}` tail bound `inverseSqrtNormTail` for later finite-range
approximants to `P^{-1/2}`.  It now also names the base kernel amplitude and
spatial convolution ratio and proves exponential decay of the shifted
non-identity inverse-square-root kernel remainder
`inverseSqrtKernelRemainder`; this respects the convention `Kpow K 0 = K`, so
identity contributions are kept outside the tail.
It also proves exact finite-range propagation for composition powers
(`Kpow_finiteRange`) and finite inverse-square-root truncation sums
(`inverseSqrtKernelTruncation_finiteRange`): if the one-step kernel has range
`R`, then `Kpow K n` has range `(n + 1)R`, and the length-`N` non-identity
truncation has range `N R`.
This is still not a physical Hessian theorem and does not construct
`P^{-1/2}` as a continuous linear map; it is reusable scalar/kernel
infrastructure for that route.
The physical frontier module
`YangMills.RG.PhysicalGaugeLocalSPDPrecisionRoot` packages normalized
finite-range physical precision data
`precision = scale • (id - normalizedPerturbation)`.  Lean derives the
coercivity constant `scale * (1 - operatorRatio)`, the upper spectral form
bound, precision self-adjointness, exact off-diagonal finite range of the
normalized perturbation and precision, the canonical exact covariance from
`covarianceOfIsCoerciveCLM`, candidate identity-plus-tail covariance/root
weights, and a constructor into the existing
`PhysicalLocalizedCovarianceRootCertificate`.  The covariance/root kernel
bounds, root square identity, root norm, root self-adjointness, root PSD, and
the separate source `root_localization` field remain explicit source
hypotheses.  The same physical package now exposes the scalar support wrappers
`kernelMajorant_Kpow_finiteRange` and
`inverseSqrtKernelTruncation_finiteRange`; these are support facts about the
majorant kernel, not a Wilson-Hessian identification or root construction.
The new CMP116 activity transport adapter narrows the final interface for that
last step: a future source theorem must supply a CMP116 localized family plus
field transports preserving `globalEval`, skeleton support localization, and
weight domination; Lean then derives the support hypotheses and `hraw` bound
consumed by Appendix F.
The corrected upstream route now also has an exact finite coordinate
dictionary in `YangMills.RG.PhysicalGaugeCMP116Dictionary`.  It identifies
flattened CMP116 scalar coordinates `Cube d L × Fin lieDim` with flattened
physical scalar coordinates `PhysicalBond dPhys N × Fin (Nc^2 - 1)`, enforces
that scalar coordinates map only inside their assigned cube, and derives the
induced pull/push maps between CMP116 coordinate fields and physical
one-cochains.  The pull/push maps are inverse and form a linear equivalence,
and `pullFluctuationCochain_agreeOn_iff` gives the exact support-agreement
translation for bonds assigned to a cube set.  The same dictionary now exposes
the pointwise bond pull `pullFluctuationAtBond`, the equality
`pullFluctuationCochain_apply`, and the image/preimage support equivalence
`image_bondToCube_subset_iff_physicalBondsOfCells`, which are consumed by the
activity adapter.  This is product-coordinate bookkeeping only: it does not
prove a physical Gaussian change of variables, root localization,
Wilson-Hessian identification, or physical raw activity decay.
The upstream route now also has a localized CMP116 operator-transport layer in
`YangMills.RG.PhysicalGaugeCMP116OperatorTransport`.  It extends
`YangMills.RG.LocalLinearOperator` with singleton cube fields, pointwise
kernel bounds, exact finite-range closures, kernel-zero support constructors,
and a bundled `CMP116LocalizedLinearMap`.  The transport file conjugates an
already supplied physical positive-bond root into CMP116 coordinates, records
the projection-compatibility and kernel-bound conversion as explicit fields,
and derives exact support/agreement/zero-output consequences for projected
finite-range root operators.  This is still not a producer of `hraw`: the
physical covariance root, its localization/truncation theorem, concrete
coordinate chart, local Wilson activities, and Appendix-F raw bounds remain
separate source obligations.
The localized-map API now exposes exact underlying-map identities for
`CMP116LocalizedLinearMap.add`, `.finsetSum`, `.comp`, and `.ofProjection`.
These are mechanical simp bridges for later finite truncation assembly; they
do not add any decay, finite-range, or source estimate.
It also exposes named support consequences for those constructors:
agreement on the declared input region and pointwise zero output outside the
declared output region.  These are exact support-algebra consumers for finite
localized-root assembly, not new localization or decay theorems.
The same API now has `CMP116LocalizedLinearMap.finsetSumVarying`, which sums a
finite family with piecewise input/output supports and certifies support on the
finite unions of those supports.  This is the concrete finite-family assembly
needed before localized root pieces can be combined.
The dictionary-backed root-transport layer now consumes that varying-support
sum API through
`PhysicalRootToCMP116OperatorTransport.localizedRootLinearMapFinsetSum_ofDictionary`.
Given a finite family of input cube sets, it sums the corresponding projected
dictionary root maps and certifies exact support from the union of those input
sets to the union of their finite-range closures.  This is still only the
support algebra of the supplied finite pieces; it does not assert that the
pieces reconstruct the full covariance root.
The same finite-piece package now exposes physical-coordinate consumers after
the dictionary pull: equality under agreement on the input-support union, and
zero output on every physical bond whose assigned cube is outside the union of
finite-range output closures.  These are direct coordinate consequences for
later local-activity support checks, not Gaussian pushforward or decay results.
It also exposes the first local-activity consumer for this finite-piece
root-sum: evaluating a physical local activity on the pulled finite-piece
output is unchanged when the CMP116 input fields agree on the declared input
union.  This consumes only `LocalActivity.globalEval_eq_of_agreeOn` and the
pulled-output equality; it does not construct local activities or prove
Gaussian-law content.
The finite-family versions now lift the same equality through an explicit
finite sum of activity evaluations and through packaged
`LocalActivity.finsetSum`, so downstream Appendix-F style finite activity
packages can consume the root-piece input-dependence theorem without opening
the single-activity proof.
The same finite-piece input-dependence theorem now also propagates through
`LocalActivity.mayerCoverActivity`, i.e. the Appendix-F raw Mayer product
`exp(H)-1` over a finite cover.  This is still exact algebra over supplied
finite root pieces, not a Gaussian pushforward or activity-decay theorem.
The activity-local bridge
`PhysicalRootToCMP116OperatorTransport.gaussianRootMap_activity_globalEval_eq_of_agreeOn_of_localizedRootLinearMapFinsetSum`
now promotes that finite-piece input locality to the actual dictionary Gaussian
root map `D.gaussianRootMap root`, but only under an explicit source-facing
agreement hypothesis on the activity's `fluctuationSupport`.  It deliberately
does not require or prove global finite-piece reconstruction of the covariance
root operator.
That obligation is now named as
`PhysicalRootToCMP116OperatorTransport.ActivityLocalRootPieceAgreement`, with
constructors from agreement on a declared physical active support and from
CMP116-domain agreement transported through the dictionary.  This makes the
current `hrootPieces` premise reusable for finite, locally finite, or
convergent root-piece routes without adding a source-hypothesis field or
claiming Balaban has supplied the missing domain/reconstruction theorem.
The dictionary-backed construction layer now has
`PhysicalRootToCMP116OperatorTransport.localizedRootLinearMap_ofDictionary`,
which turns an explicit physical root kernel bound, a dictionary kernel-bound
transport, and a finite-range CMP116 weight into the exact
`CMP116LocalizedLinearMap` support package consumed by later local activity
construction.  This is still a transport/support constructor, not a source
proof of the physical root kernel bound or the finite-range weight.
The Gaussian-change source package now has its first physical-activity
consumer:
`PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses.integral_physicalActivity_gaussianRootMap_eq`
specializes the canonical source-package integral rewrite to
`PhysicalGaugeLocalActivity.globalEval`.  This is the direct form needed by
source-faithful activity estimates after the physical fluctuation field is
pulled back through `D.gaussianRootMap root`.  It still assumes the source
`gaussian_pushforward` theorem and does not prove root localization,
Wilson-Hessian identification, local activity construction, raw decay, or
`hraw`.
The same dictionary/root map now has the exact operator-coordinate identity
`PhysicalGaugeCMP116Dictionary.gaussianRootMap_eq_coordinates_comp_cmp116OperatorOfPhysical`:
the physical map `D.gaussianRootMap root` is precisely the physical-coordinate
realization of the root conjugated into CMP116 coordinates.  This is a
definition-level algebra bridge, not a Gaussian-law or localization theorem.
The dictionary/root construction layer also exposes two-sided norm-control
lemmas for the dictionary pull/push maps:
`PhysicalGaugeCMP116Dictionary.norm_pullFluctuationCochain_le`,
`norm_pushFluctuation_le`,
`norm_le_inverse_opNorm_mul_norm_pullFluctuationCochain`, and
`norm_le_opNorm_mul_norm_pushFluctuation`.  These record only generic operator
norm bounds for the continuous dictionary equivalence and its inverse; they do
not assert an isometry, a Jacobian convention, or any physical Gaussian law.
The canonical Gaussian coordinate map now has the corresponding operator and
pointwise norm budgets
`PhysicalGaugeCMP116Dictionary.norm_gaussianRootMap_le`,
`norm_gaussianRootMap_apply_le`,
`norm_gaussianRootMap_le_of_root_norm_le`, and
`norm_gaussianRootMap_apply_le_of_root_norm_le`.  These combine the root
operator norm with the dictionary norm constant; they still do not prove the
Gaussian pushforward identity or any covariance-root localization.
The same budget can now be consumed directly from a localized covariance-root
certificate via
`PhysicalGaugeCMP116Dictionary.norm_gaussianRootMap_le_of_covarianceRootCertificate`
and
`PhysicalGaugeCMP116Dictionary.norm_gaussianRootMap_apply_le_of_covarianceRootCertificate`.
These are projection lemmas for the existing `root_norm_bound` certificate
field, not new root construction or localization estimates.
The downstream transport package now exposes the same budget through
`PhysicalGaugeCMP116ActivityTransport.norm_gaussianRootMap_le` and
`PhysicalGaugeCMP116ActivityTransport.norm_gaussianRootMap_apply_le`, so a
constructed physical/CMP116 activity transport can feed later estimates with
the explicit dictionary norm constant still visible.
The same construction file now has a thin raw-source compatibility layer:
`PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses` extends the
separated Gaussian/root/Hessian/activity source package with the unfolded
pointwise raw estimate, and Lean derives
`physicalGaugeRawActivityDecay_of_cmp116RawSource` plus
`physicalLocalizedGaussianActivityCertificate_of_cmp116RawSource`.  This
removes one adapter redundancy for future CMP116 transport calls without
changing the analytic frontier: the raw estimate is still a source hypothesis,
not a theorem proved from Balaban/CMP116 inputs.
The raw-source package now also has direct CMP116 consumers:
`PhysicalGaugeCMP116ActivityTransport.of_cmp116RawSource`,
`physicalGaugeCMP116ActivityTransport_of_cmp116RawSource`,
`physicalGaugeCMP116SupportHypotheses_of_cmp116RawSource`,
`balabanCMP116RawMetricDecay_of_cmp116RawSource`, and
`balabanCMP116_hraw_of_cmp116RawSource`.  These compose the existing
dictionary transport, support localization, weight domination, and raw-source
decay adapters, so a single raw-source package plus the still-explicit
measurability/support/weight hypotheses yields the canonical transport,
Appendix-F support package, and exact Appendix-F `hraw` shape.  This is still
conditional plumbing; it does not prove the source activity estimate,
integrability, or the analytic support/weight hypotheses.
The follow-on module `YangMills/RG/PhysicalGaugeCMP116RawHsharp.lean` packages
the same raw-source construction as a scale-indexed CMP116 family and feeds it
directly to the existing source-measurable H# endpoint via
`singleScaleUVDecay_of_cmp116RawSource_hsharp`.  This discharges only the H#
`hraw` premise from the raw-source package; the rooted remainder identity,
probability law, hole geometry, smallness/profile inequalities,
integrability, and actual physical source estimates remain explicit.
The marginal M3 branch now has the named predicate consumer
`lattice_mass_gap_of_singleScaleUVDecay_marginal`, and
`YangMills/RG/PhysicalGaugeCMP116RawM3.lean` routes the raw-source H# producer
through it via `lattice_mass_gap_of_cmp116RawSource_hsharp_marginal`.  This
removes the intermediate top-level `SingleScaleUVDecay` premise from that
conditional M3 endpoint, while keeping the raw-source/H# hypotheses, marginal
flow recursion, positivity/smallness of `g`, and IR bound explicit.
The follow-on frontier module
`YangMills/RG/PhysicalGaugeCMP116RawHsharpFrontier.lean` names that full
raw-source/H# hypothesis boundary as
`PhysicalGaugeCMP116RawHsharpFrontier` and projects it into both
`singleScaleUVDecay` and the marginal M3 consumer.  This makes the remaining
source obligations auditable as one bundle; it does not prove the Hessian,
Gaussian pushforward, covariance-root localization, source activity, H#
profile, marginal-flow, or IR estimates.
The M3-specific wrapper in `YangMills/RG/PhysicalGaugeCMP116RawM3.lean` now
also exposes `CMP116RawSourceM3Frontier` and
`lattice_mass_gap_of_cmp116RawSourceM3Frontier`, bundling the raw-source/H#
frontier together with the marginal-flow and IR consumer-side hypotheses.  The
truncation schedule remains a theorem parameter rather than a frontier field,
because no frontier hypothesis constrains it.
The dependency graph for that frontier is now executable in
`YangMills/RG/M3FrontierDependencies.lean`, with one graph node per frontier
field, role classifications, derived nodes for the raw-source scale family,
H# UV decay, and M3 assembly, and Boolean/theorem checks for acyclicity and
field coverage.  It now also checks that every frontier field is consumed by at
least one derived-node input list, so the audit catches both missing nodes and
currently unused frontier fields.  The companion note is
[`docs/M3-FRONTIER-DEPENDENCIES.md`](docs/M3-FRONTIER-DEPENDENCIES.md).
The source-facing theorem target for that frontier is now stated in
`YangMills/RG/BalabanCMP116SourceTheorem.lean`.  It adds the pure constructor
`PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.of_components`
and the checked proposition `BalabanCMP116SourceTheorem`, splitting the current
opaque `raw_source` package into Gaussian pushforward, root localization,
Wilson-Hessian identification, local physical activity construction, and raw
pointwise decay fields.  No Balaban source theorem or frontier witness is
proved by this target declaration.  The helper
`BalabanCMP116SourceAssumptions.rawSource` now provides the canonical
scale-indexed projection from those five unfolded source fields back to the
existing raw-source package, without constructing the full frontier.  The
projection-consistency theorem
`BalabanCMP116SourceAssumptions.rooted_hsharp_remainder_identity_rawSource`
restates the record's rooted H# identity using that canonical raw-source
projection; it does not prove the physical remainder identity itself.
The pure packaging constructor
`CMP116RawSourceM3Frontier.of_balabanSourceAssumptions`, its method-style alias
`BalabanCMP116SourceAssumptions.to_m3Frontier`, and
`balabanCMP116SourceTheorem_of_assumptions` now close the named
`BalabanCMP116SourceTheorem` implication.  This consumes every source field but
does not prove any source field.

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

The CMP116 Lemma-3 residual route now also has a combined post-`P` residual
budget interface:
`CMP116PostPResidualSourceBound`,
`cmp116PostPResidualBound_of_sourceBound`,
`CMP116PostPResidualSourceMajorizationScaleFamily`,
`cmp116PostPResidualBoundScaleFamily_of_sourceBound`,
`CMP116PostPResidualBound`,
`cmp116H_postD_sum_le_of_pStagePostPResidualBound`,
`cmp116H_termWeightSum_le_of_eq229_of_pStagePostPResidualBound`,
`cmp116Lemma3ActivityEstimate_of_eq229_pStagePostPResidualBound`, and
`cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStagePostPResidualBound`.
This was added after rechecking CMP116 printed pages 19--20: the source
controls the final `Z0/Z0'` resummations in a combined/order-sensitive way, so
the repository must not pretend that the normalized `Z0'` predicate has been
separately source-identified.  The source-bound adapter keeps the printed
source amplitude/weight separate from the canonical Lemma-3 base factor and
requires an explicit majorization theorem.  The scale-family majorization
predicate now names this base-factor comparison at every `(t, k)`, and the
scale-family adapter applies the existing single-scale post-`P` residual
consumer pointwise when the source bound and `P`-weight nonnegativity are
supplied.  The new route is still conditional; it does not prove Eq. (2.29),
the P-stage budget, activity identification, termwise estimates, the
majorization, or the combined post-`P` source estimate.

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
