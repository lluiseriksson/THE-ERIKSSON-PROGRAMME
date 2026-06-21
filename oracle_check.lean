import YangMillsCore
import YangMills.RG.NearLog
import YangMills.RG.LocalFunctional
import YangMills.RG.RawMayerWithHoles
import YangMills.RG.OmegaConnectedCover
import YangMills.RG.MayerCoverFactorization
import YangMills.RG.AppendixFFiniteCover
import YangMills.RG.AppendixFHoleTarget
import YangMills.RG.AppendixFKsharp
import YangMills.RG.AppendixFQuantitative
import YangMills.RG.AppendixFFiberEntropy
import YangMills.RG.PolymerClusterWithHolesBridge
import YangMills.RG.AppendixFLocalSummability
import YangMills.RG.AppendixFKsharpEstimate
import YangMills.RG.AppendixFSecondGas
import YangMills.RG.AppendixFHsharp
import YangMills.RG.AppendixFHsharpResidual
import YangMills.RG.AppendixFHsharpPartial
import YangMills.RG.AppendixFHsharpConvergence
import YangMills.RG.AppendixFHsharpLimit
import YangMills.RG.AppendixFHsharpMajorant
import YangMills.RG.AppendixFHsharpGeometricMajorant
import YangMills.RG.AppendixFHsharpSourceMajorant
import YangMills.RG.AppendixFSecondUrsellSource
import YangMills.RG.AppendixFCluster3Geometry
import YangMills.RG.AppendixFHsharpCluster3
import YangMills.RG.AppendixFHsharpProfile

/-! # Oracle check — one command, every headline

`lake env lean oracle_check.lean`

Every result below must print exactly
`[propext, Classical.choice, Quot.sound]` — Lean's three standard
axioms; no `sorry`, no project axioms.  The authoritative record of
these outputs over time is `docs/VERIFICATION-LEDGER.md`. -/

/-! ## The Haar-integration engines -/
#print axioms YangMills.haar_integral_eq_zero_of_center_eigenfunction
#print axioms YangMills.integral_eq_zero_of_left_invariant_eigenfunction

/-! ## The Z_N selection rules (characters → matrix coefficients) -/
#print axioms YangMills.sunHaarProb_trace_pow_complex_integral_zero
#print axioms YangMills.sunHaarProb_trace_mixedPow_integral_zero
#print axioms YangMills.sunHaarProb_fundMonomial_integral_zero
#print axioms YangMills.sunHaarProb_tracematpow_integral_zero
#print axioms YangMills.sunHaarProb_tracematpow_mixed_integral_zero
-- off-diagonal matrix-coefficient vanishing: ∫ U_{ij} · conj(U_{kl}) = 0 when i ≠ k
-- (L2.6 step 1b-ii; repaired back into the verified core, ledger Addendum 85)
#print axioms YangMills.ClayCore.sunHaarProb_entry_offdiag

/-! ## SU(1) degeneracy and U(1) exact orthogonality -/
#print axioms YangMills.specialUnitaryGroup_fin_one_eq_one
#print axioms YangMills.integral_fourier_eq_indicator
#print axioms YangMills.integral_fourier_mul_conj_eq_indicator

/-! ## The cluster-expansion layer (sharp KP + Mayer inversion) -/
#print axioms YangMills.KP.partition_eq_exp_clusterSum
#print axioms YangMills.KP.partition_eq_exp_clusterSum_of_kp
#print axioms YangMills.KP.scaleActivity_exp_norm_activity_mul_exp
#print axioms YangMills.KP.orderFactor_pinnedClusterWeight_le_tilt
#print axioms YangMills.KP.summable_finset_pinnedClusterWeight
#print axioms YangMills.KP.tsum_finset_pinnedClusterWeight_le
#print axioms YangMills.KP.rootedChildren
#print axioms YangMills.KP.rootedChildCount
#print axioms YangMills.KP.mem_rootedChildren
#print axioms YangMills.KP.rootedChild_ne_zero
#print axioms YangMills.KP.rootedChild_parent_eq
#print axioms YangMills.KP.mem_rootedChildren_parent
#print axioms YangMills.KP.rootedChild_parent_unique
#print axioms YangMills.KP.disjoint_rootedChildren_of_ne
#print axioms YangMills.KP.biUnion_rootedChildren_eq_nonroot
#print axioms YangMills.KP.rootedChild_parent_edge_mem
#print axioms YangMills.KP.sum_rootedChildCount_eq
#print axioms YangMills.KP.card_rootedChildOrderAssignments
#print axioms YangMills.KP.prod_factorial_dvd_factorial_sum
#print axioms YangMills.KP.prod_factorial_le_factorial_sum
#print axioms YangMills.KP.rootedChildCount_factorialProduct_dvd_factorial
#print axioms YangMills.KP.rootedChildCount_factorialProduct_le_factorial
#print axioms YangMills.KP.rootedChildCount_factorialProduct_real_le_factorial
#print axioms YangMills.KP.rootedChildCount_factorialProduct_inv_succ_factorial_le_inv_succ
#print axioms YangMills.KP.parentMapProfileCount_le_four_pow
#print axioms YangMills.KP.sum_parentMapChildCount_factorialProduct_le_factorial_mul_four_pow
#print axioms YangMills.KP.sum_rootedChildCount_factorialProduct_le_factorial_mul_four_pow
#print axioms YangMills.KP.rootedChildCount_factorialTreeSum_normalized_le_four_pow

/-! ## The IR clustering bound and the correlator decay -/
#print axioms YangMills.truncated_correlation_bound
#print axioms YangMills.gibbs_truncated_correlation_bound
#print axioms YangMills.sun_two_plaquette_correlator_bound
-- UNCONDITIONAL fixed-lattice exponential clustering (no carried hypothesis):
#print axioms YangMills.sun_lattice_exponential_clustering

/-! ## The M3 mass-gap assembly (UV bound carried as a hypothesis) -/
#print axioms YangMills.lattice_mass_gap_of_clustering_uniform
#print axioms YangMills.lattice_mass_gap_of_exp_clustering_uniform
-- UV brick U0: the carried hypothesis sharpened to a per-scale RG contraction
#print axioms YangMills.lattice_mass_gap_of_per_scale_uv
-- Gap-refinement obstruction: arbitrarily small positive excitations defeat a
-- positive gap, and stagewise regulator gaps need not give a uniform gap.
#print axioms YangMills.not_hasPositiveEnergyGap_of_arbitrarilySmallPositiveExcitations
#print axioms YangMills.not_hasUniformPositiveEnergyGap_of_refinementsProduceArbitrarilySmallPositiveExcitations
#print axioms YangMills.halfScaleExcitation_stagewise_but_not_uniform

/-! ## The Wilson-loop area laws — finite volume -/
#print axioms YangMills.finite_volume_area_law          -- linearized activities
#print axioms YangMills.finite_volume_area_law_re       -- physical Re tr observable
#print axioms YangMills.norm_integral_exp_term_le       -- per-multiplicity dichotomy
#print axioms YangMills.finite_volume_area_law_exp      -- TRUE Wilson factor

/-! ## The Wilson-loop area laws — VOLUME-UNIFORM (the flagship) -/
#print axioms YangMills.normalized_wilson_loop_area_law              -- linearized, normalized by Z
#print axioms YangMills.normalized_wilson_loop_area_law_unconditional -- integrability discharged
#print axioms YangMills.normalized_exp_wilson_loop_area_law          -- TRUE Wilson factor, volume-uniform
#print axioms YangMills.area_law_to_exp_area_decay                   -- manifest exp area decay (confinement)

/-! ## Non-vacuity witnesses (the exponent, the windows, the tension are real) -/
#print axioms YangMills.one_le_chainAreaA_plaquette
#print axioms YangMills.clustering_window_nonempty
#print axioms YangMills.sun_clustering_window_nonempty
#print axioms YangMills.area_law_to_exp_area_decay_window_nonempty    -- positive string tension log 2 − ½

/-! ## The gauge-RG continuum track (`YangMills/RG/**`) — the §6.3 UV branch

All carried gaps are explicit theorem hypotheses, never axioms; every
result below is oracle-clean.  The §6.3 UV obligation is the single
end-to-end conditional `lattice_mass_gap_of_cluster_and_coupling` on two
faithful Bałaban inputs (`hRpoly`, `hg`).  See `docs/BALABAN-RG-PLAN.md`,
`docs/BALABAN-SOURCE-BOUNDS.md`, `HYPOTHESIS_FRONTIER.md`. -/

-- End-to-end UV conditional: (cluster activity bound + coupling decay) ⟹ lattice mass gap
#print axioms YangMills.RG.lattice_mass_gap_of_cluster_and_coupling
-- tighter form: coupling decay discharged from the logistic RG recursion
#print axioms YangMills.RG.lattice_mass_gap_of_cluster_and_logistic_coupling
-- non-vacuity: the end-to-end conditional's hypotheses are jointly satisfiable (nonzero data)
#print axioms YangMills.RG.lattice_mass_gap_uv_conditional_nonvacuous
-- the coupling-flow bridge (faithful polymer bound + coupling decay ⟹ M·rᵏ surrogate)
#print axioms YangMills.RG.coupling_flow_bridge
-- coupling-flow decay from the irrelevant logistic recursion; full assembled conditional
#print axioms YangMills.RG.remainder_geometric_of_logistic
#print axioms YangMills.RG.geometric_remainder_assembled
-- asymptotic freedom: the 4D MARGINAL coupling decays only logarithmically (1/g_n ≥ 1/g_0 + βn)
#print axioms YangMills.RG.inv_coupling_linear_growth
-- the polymer cluster-sum bound + the KP/Appendix-F geometric summability core
#print axioms YangMills.RG.polymer_remainder_bound
#print axioms YangMills.RG.geometric_size_summability
-- the summability `hwK` reduced to the polymer animal-count `c_n ≤ Cⁿ`
#print axioms YangMills.RG.polymer_weight_summability
-- hRpoly campaign brick P1a: the bounded-degree walk-count engine `≤ Δⁿ`
-- (combinatorial substrate of the animal count `c_n ≤ Cⁿ`)
#print axioms YangMills.RG.card_walks_length_le_degree_pow
-- hRpoly campaign brick P1b-ii (engine): the detour splice — the inductive
-- step of the tree Euler tour (add a leaf, length +2, support +{u})
#print axioms YangMills.RG.exists_detour_walk
-- hRpoly campaign bricks P1b/P1c: the farthest-vertex peel, the spanning
-- closed walk (full tour), and the lattice animal count `c_n ≤ Δ^{2(n-1)}`
#print axioms YangMills.RG.exists_peel
#print axioms YangMills.RG.exists_spanning_closed_walk
#print axioms YangMills.RG.animal_card_le
-- the animal count as a cardinal (`c_n ≤ Cⁿ`) and **branch C closed**: the
-- geometric summability `hwK` discharged from the animal count
#print axioms YangMills.RG.rooted_connected_card_le_pow
#print axioms YangMills.RG.rooted_connected_weight_summable
-- P2 geometry: the M-cube king-adjacency degree bound ≤ 3^d and the concrete
-- cube-lattice polymer summability on Dimock's geometry
#print axioms YangMills.RG.cubeAdj_degree_le
#print axioms YangMills.RG.cube_polymer_summable
-- the YM coupling is marginal (asymptotically free), NOT geometric: the marginal
-- coupling still yields a summable scale-series for activity power κ₀ > 1
#print axioms YangMills.RG.marginal_coupling_pow_summable
#print axioms YangMills.RG.marginal_coupling_tendsto_zero
-- the marginal-coupling remainder scale-sum bound (honest YM coupling bridge)
#print axioms YangMills.RG.marginal_coupling_remainder_tsum_le
-- the summable-profile UV assembly + the honest YM end-to-end UV conditional
-- with the MARGINAL coupling (no geometric assumption)
#print axioms YangMills.RG.lattice_mass_gap_of_per_scale_uv_summable
#print axioms YangMills.RG.lattice_mass_gap_of_cluster_and_marginal_coupling
-- non-vacuity: the marginal-coupling recursion is satisfiable (logistic flow)
#print axioms YangMills.RG.exists_marginal_coupling_flow
-- semantic producer/consumer split: renormalized hole activities imply the
-- scalar single-scale UV decay consumed by the mass-gap assembly
#print axioms YangMills.RG.singleScaleUVDecay_of_renormalizedHoleActivities
#print axioms YangMills.RG.lattice_mass_gap_of_singleScaleUVDecay_geometric
-- residual with-holes bridge: Appendix-F loss `κ - 3κ₀ - 3`, the stronger
-- summability margin `κ₀ ≤ κ - 3κ₀ - 3`, and the resulting `hpoly` producer
#print axioms YangMills.RG.polymerClusterResidualRate_nonneg_of_three_mul_add_le
#print axioms YangMills.RG.kappa0_le_polymerClusterResidualRate_of_four_mul_add_le
#print axioms YangMills.RG.polymerClusterWithHoles_abs_tsum_le
#print axioms YangMills.RG.exp_neg_kappa0_nat_eq_exp_neg_pow
#print axioms YangMills.RG.rooted_exp_discreteModifiedMetric_tsum_le
#print axioms YangMills.RG.rooted_polymerClusterWithHoles_abs_tsum_le
#print axioms YangMills.RG.omegaRootedPolymerEquiv
#print axioms YangMills.RG.omega_rooted_exp_discreteModifiedMetric_tsum_le
#print axioms YangMills.RG.omega_rooted_polymerClusterWithHoles_abs_tsum_le
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedClusterWithHolesActivities
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedClusterWithHolesActivities_four_mul_margin
#print axioms YangMills.RG.renormalizedHoleActivityDecay_of_clusterWithHolesActivityDecay
#print axioms YangMills.RG.singleScaleUVDecay_of_clusterWithHolesActivities
-- type-local support substrate for constructive Dimock F.1 activities
#print axioms YangMills.RG.LocalFunctional.globalEval_eq_of_agreeOn
#print axioms YangMills.RG.LocalFunctional.globalEval_finsetProd
#print axioms YangMills.RG.LocalActivity.globalEval_eq_of_agreeOn
#print axioms YangMills.RG.LocalActivity.globalEval_finsetProd
#print axioms YangMills.RG.LocalActivity.globalEval_finsetSum
#print axioms YangMills.RG.LocalActivity.globalEval_integrateFluctuation
#print axioms YangMills.RG.LocalActivity.norm_globalEval_integrateFluctuation_le_of_norm_le
-- ultralocal product-measure factorization for disjoint type-local supports
#print axioms YangMills.RG.LocalFunctional.integral_mul_of_disjoint_support
#print axioms YangMills.RG.LocalActivity.integral_mul_of_disjoint_fluctuationSupport
-- raw Mayer transform on type-local supports
#print axioms YangMills.RG.LocalFunctional.rawMayer_globalEval_eq_of_agreeOn
#print axioms YangMills.RG.LocalFunctional.norm_globalEval_rawMayer_le_two
#print axioms YangMills.RG.LocalActivity.rawMayer_globalEval_eq_of_agreeOn
#print axioms YangMills.RG.LocalActivity.norm_globalEval_rawMayer_le_two
-- Ω-connected cover substrate and Mayer-cover product
#print axioms YangMills.RG.omegaOverlapGraph_adj_iff
#print axioms YangMills.RG.LocalActivity.globalEval_mayerCoverActivity
#print axioms YangMills.RG.LocalActivity.norm_globalEval_mayerCoverActivity_le_prod_two_of_norm_le
#print axioms YangMills.RG.LocalActivity.norm_globalEval_mayerCoverActivity_le_two_mul_pow_card_of_norm_le
#print axioms YangMills.RG.LocalActivity.norm_globalEval_mayerCoverActivity_le_two_mul_pow_of_le_card
#print axioms YangMills.RG.LocalActivity.mayerCoverActivity_fluctuationSupport_subset_omega_biUnion_activeSupport
#print axioms YangMills.RG.LocalActivity.mayerCoverActivity_globalEval_eq_of_agreeOn
#print axioms YangMills.RG.OmegaConnectedCover.globalEval_mayerActivity
#print axioms YangMills.RG.OmegaConnectedCover.norm_globalEval_mayerActivity_le_prod_two_of_norm_le
#print axioms YangMills.RG.OmegaConnectedCover.norm_globalEval_mayerActivity_le_two_mul_pow_card_of_norm_le
#print axioms YangMills.RG.OmegaConnectedCover.norm_globalEval_mayerActivity_le_two_mul_pow_of_le_card
#print axioms YangMills.RG.OmegaConnectedCover.mayerActivity_fluctuationSupport_subset_omega_biUnion_activeSupport
#print axioms YangMills.RG.OmegaConnectedCover.mayerActivity_globalEval_eq_of_agreeOn
-- ultralocal independence for finite Mayer-cover products
#print axioms YangMills.RG.mem_confinedComponent_of_mem_confinedWalk_support
#print axioms YangMills.RG.confinedComponent_walkConnected
#print axioms YangMills.RG.no_adj_confinedComponent_compl
#print axioms YangMills.RG.biUnion_confinedComponents_eq
#print axioms YangMills.RG.confinedComponents_eq_of_nonempty_inter
#print axioms YangMills.RG.disjoint_of_mem_confinedComponents_ne
#print axioms YangMills.RG.no_adj_of_mem_confinedComponents_ne
#print axioms YangMills.RG.OmegaConnectedCover.confinedComponentCover
#print axioms YangMills.RG.OmegaConnectedCover.mayerActivity_confinedComponentCover
#print axioms YangMills.RG.OmegaConnectedCover.exists_confinedComponentCover_of_mem_confinedComponents
#print axioms YangMills.RG.OmegaConnectedCover.confinedComponentCoverOfComponent
#print axioms YangMills.RG.OmegaConnectedCover.mayerActivity_confinedComponentCoverOfComponent
#print axioms YangMills.RG.OmegaConnectedCover.confinedComponentCoverFamily
#print axioms YangMills.RG.OmegaConnectedCover.biUnion_confinedComponentCoverFamily_index_eq
#print axioms YangMills.RG.OmegaConnectedCover.disjoint_confinedComponentCoverFamily_index_of_ne
#print axioms YangMills.RG.OmegaConnectedCover.pairwise_disjoint_confinedComponentCoverFamily_index
#print axioms YangMills.RG.OmegaConnectedCover.omegaActiveSupport_disjoint_of_mem_confinedComponents_ne
#print axioms YangMills.RG.OmegaConnectedCover.pairwise_omegaActiveSupport_disjoint_of_mem_confinedComponents_ne
#print axioms YangMills.RG.OmegaConnectedCover.pairwise_omegaActiveSupport_disjoint_confinedComponentCoverFamily
#print axioms YangMills.RG.OmegaConnectedCover.mayerActivity_integral_factor_confinedComponentCoverFamily_of_fluctuationSupport_subset
#print axioms YangMills.RG.LocalActivity.fluctuationOverlapGraph_adj_iff
#print axioms YangMills.RG.LocalActivity.fluctuationOverlapGraph_adj_imp_omegaOverlapGraph_adj_of_fluctuationSupport_subset
#print axioms YangMills.RG.LocalActivity.pairwise_disjoint_fluctuationSupport_of_no_cross_adj
#print axioms YangMills.RG.LocalActivity.globalEval_mayerCoverActivity_union
#print axioms YangMills.RG.LocalActivity.mayerCoverActivity_integral_mul_of_pairwise_disjoint_fluctuationSupport
#print axioms YangMills.RG.LocalActivity.mayerCoverActivity_union_integral_of_pairwise_disjoint_fluctuationSupport
#print axioms YangMills.RG.LocalActivity.mayerCoverActivity_union_integral_of_no_cross_fluctuationAdj
#print axioms YangMills.RG.LocalActivity.mayerCoverActivity_integral_split_confinedComponent
#print axioms YangMills.RG.LocalActivity.mayerCoverActivity_biUnion_integral_of_no_cross_components
#print axioms YangMills.RG.LocalActivity.mayerCoverActivity_integral_factor_confinedComponents
#print axioms YangMills.RG.LocalActivity.mayerCoverActivity_integral_factor_confinedOmegaComponents_of_fluctuationSupport_subset
#print axioms YangMills.RG.OmegaConnectedCover.mayerActivity_integral_mul_of_pairwise_disjoint_fluctuationSupport
-- decoupling/regularisation bridge: a uniform activity profile bound passes to
-- the pointwise limiting activity, and a summable telescopic regulator defect
-- increases only the amplitude budget.
#print axioms YangMills.RG.activity_profile_bound_of_tendsto
#print axioms YangMills.RG.activity_profile_bound_of_finite_telescope
#print axioms YangMills.RG.activity_profile_bound_of_tendsto_telescope
-- finite-range ⟹ ExpDecay (the operator-level Combes-Thomas input: nearest-
-- neighbour Laplacian / Wilson hopping / covariant difference operators)
#print axioms YangMills.RG.finiteRange_isExpDecay
-- exponential-decay kernel calculus: composition (Combes-Thomas engine), sum
#print axioms YangMills.RG.expDecay_comp
#print axioms YangMills.RG.expDecay_add
-- asymmetric composition + fixed-rate iterated composition (Neumann engine)
#print axioms YangMills.RG.expDecay_comp_asym
#print axioms YangMills.RG.expDecay_pow
-- resolvent / Neumann-series decay (the Combes-Thomas conclusion)
#print axioms YangMills.RG.expDecay_resolvent
-- concrete Combes-Thomas: the resolvent of a small finite-range operator decays
-- exponentially (the literal mechanism of the Balaban propagator bound)
#print axioms YangMills.RG.finiteRange_resolvent_isExpDecay
-- volume-uniform lattice exponential summability from a shell-growth bound
-- (discharges the recurring geometric hypothesis of the whole decay stack)
#print axioms YangMills.RG.lattice_exp_sum_le_of_shell
-- explicit closed-form constant S = C·(1−r·e^{−σ})⁻¹ for a bounded-degree lattice
#print axioms YangMills.RG.lattice_exp_sum_le_geometric
-- Schur boundedness: row-sum + quadratic-form (covariance) bound ≤ a·S
#print axioms YangMills.RG.expDecay_finset_row_le
-- collar-separated cross interaction: ExpDecay + separation ε pays exp(-κ ε)
#print axioms YangMills.RG.expDecay_separated_finset_sum_le
#print axioms YangMills.RG.expDecay_quadratic_form_le
-- the full ℓ² Schur test: operator-norm bound ‖K‖op ≤ a·S
#print axioms YangMills.RG.expDecay_op_bilinear_le
-- PSD covariance-kernel interface: variance ≥ 0 and the covariance Cauchy–Schwarz
#print axioms YangMills.RG.psd_diag_nonneg
#print axioms YangMills.RG.psd_cauchy_schwarz
-- Gaussian field-size / MGF bound from a covariance bound (fluctuation input)
#print axioms YangMills.RG.gaussian_exp_integral_le
-- self-contained MGF bound for an abstract centered IsGaussian measure
#print axioms YangMills.RG.gaussian_exp_integral_le_isGaussian
-- the concrete multivariate Gaussian as an IsGaussian measure (missing primitive)
-- and its closure under continuous-linear images (constructive covariance route)
#print axioms YangMills.RG.isGaussian_pi
#print axioms YangMills.RG.isGaussian_pi_map_clm
-- the standard multivariate Gaussian is centered, and the resulting fully
-- concrete (non-abstract) field-size / MGF bound instantiated on it
#print axioms YangMills.RG.pi_gaussian_centered
#print axioms YangMills.RG.pi_gaussian_exp_integral_le
-- the variance bridge: covariance form of the product Gaussian computed as a
-- diagonal sum, and the field-size bounds it feeds (Schur/PSD → variance → MGF)
#print axioms YangMills.RG.pi_gaussian_variance
#print axioms YangMills.RG.pi_gaussian_exp_integral_le_of_covariance_sum
#print axioms YangMills.RG.pi_gaussian_exp_integral_le_of_uniform_variance
-- general (off-diagonal) covariance via the A-pushforward: variance form + field-size bound
#print axioms YangMills.RG.pi_gaussian_map_variance
#print axioms YangMills.RG.pi_gaussian_map_exp_integral_le
-- the faithful closure: covariance = Gram quadratic form of its kernel, and an
-- ExpDecay covariance kernel ⟹ Gaussian field-size bound (Schur → variance → MGF)
#print axioms YangMills.RG.pi_gaussian_map_variance_quadratic
#print axioms YangMills.RG.pi_gaussian_map_exp_integral_le_of_expDecay
-- the constructed Gram covariance kernel is a genuine PSD kernel (non-vacuity)
#print axioms YangMills.RG.gram_kernel_isPSDKernel

/-! ### Gauge covariance and the averaging operator -/
-- gauge covariance of the Ū-block (CMP 109 (0.12)) and the lattice realization bridge
#print axioms YangMills.RG.UbarBlock_conj
#print axioms YangMills.RG.rep_wilsonLine_gaugeAct
-- the ℓ²(lattice) operator contraction of Q (L^{2-d}; a contraction for d ≥ 4)
#print axioms YangMills.RG.linAvg_l2_contraction
-- finite-stencil locality for Q and its scaled Hilbert-space operator
#print axioms YangMills.RG.linAvg_congr_of_eqOn_support
#print axioms YangMills.RG.scaledLinAvgCLM_congr_of_eqOn_support
-- Hilbert-space Q†Q mass: energy identity, PSD, and operator-norm control
#print axioms YangMills.RG.inner_qMassCLM_self
#print axioms YangMills.RG.qMassCLM_psd
#print axioms YangMills.RG.qMassCLM_opNorm_le
-- the free RG step's covariance transformation law (on Mathlib's IsGaussian)
#print axioms YangMills.RG.covarianceBilinDual_map_clm
-- finite Gaussian block collar: normalization of translated kernels and product block transforms
#print axioms YangMills.RG.gaussianBlockKernel_isProbability
#print axioms YangMills.RG.gaussianBlockTransform_isProbability
-- Gaussian closure of the finite collar under translation, product, and the linear block map
#print axioms YangMills.RG.gaussianBlockKernel_isGaussian
#print axioms YangMills.RG.gaussianBlockTransform_isGaussian

/-! ### The near-identity matrix-logarithm calculus -/
-- the quantitative axiom (0.8): exp(nearLog Y) = 1 + Y + O(‖Y‖²)
#print axioms YangMills.RG.norm_exp_nearLog_sub_one_sub_self_le
-- near-identity dictionary: ‖Y‖ and ‖nearLog Y‖ control each other locally
#print axioms YangMills.RG.norm_nearLog_two_sided_of_norm_le_third
-- scalar correctness (non-vacuity: nearLog IS the logarithm) + conjugation-equivariance
#print axioms YangMills.RG.nearLog_real
#print axioms YangMills.RG.nearLog_conj

/-! ### Approximate Ward cancellation -/
-- Abstract SUSY/cohomological cancellation interface: cancel Q-exact pieces
-- before applying absolute values, with an explicit Ward defect.
#print axioms YangMills.SUSY.expect_Q_eq_zero_of_defect_eq_zero
#print axioms YangMills.SUSY.expect_decomposition_bound
#print axioms YangMills.SUSY.expect_decomposition_profile_bound
#print axioms YangMills.SUSY.expect_profile_bound_of_exact_ward
-- Algebraic finite Berezin substrate: top exterior coefficient functional.
#print axioms YangMills.SUSY.finiteExteriorBasis_empty
#print axioms YangMills.SUSY.finiteBerezinTop_basis
#print axioms YangMills.SUSY.finiteBerezinTop_top_basis
#print axioms YangMills.SUSY.finiteBerezinTop_basis_of_ne_top
#print axioms YangMills.SUSY.finiteBerezinTop_one_of_pos
#print axioms YangMills.SUSY.finiteBerezinTop_one_zero
#print axioms YangMills.SUSY.finiteBerezinTop_algebraMap_of_pos
#print axioms YangMills.SUSY.finiteBerezinEmptyCoeff_basis
#print axioms YangMills.SUSY.finiteBerezinEmptyCoeff_empty_basis
#print axioms YangMills.SUSY.finiteBerezinEmptyCoeff_basis_of_nonempty
#print axioms YangMills.SUSY.finiteBerezinEmptyCoeff_one
#print axioms YangMills.SUSY.finiteBerezinTop_sum_basis_eq_if_mem
#print axioms YangMills.SUSY.finiteBerezinEmptyCoeff_sum_basis_eq_if_mem
#print axioms YangMills.SUSY.finiteBerezinWeighted_apply
#print axioms YangMills.SUSY.finiteBerezinWeighted_one
#print axioms YangMills.SUSY.finiteBerezinWeighted_top_basis_one
#print axioms YangMills.SUSY.finiteBerezinTopWeight_zero
#print axioms YangMills.SUSY.finiteBerezinWeighted_topWeight_one_of_pos
#print axioms YangMills.SUSY.finiteBerezinWeighted_topWeight_algebraMap_of_pos
#print axioms YangMills.SUSY.finiteExteriorBasis_powersetCard_mul_of_not_disjoint
#print axioms YangMills.SUSY.finiteExteriorBasis_powersetCard_mul_of_disjoint
#print axioms YangMills.SUSY.finiteExteriorBasis_mul_of_not_disjoint
#print axioms YangMills.SUSY.finiteBerezinTop_basis_mul_of_not_disjoint
#print axioms YangMills.SUSY.finiteBerezinTop_powersetCard_mul_of_disjoint_top
#print axioms YangMills.SUSY.finiteExteriorBasis_univ_mul_of_nonempty
#print axioms YangMills.SUSY.finiteExteriorBasis_mul_univ_of_nonempty
#print axioms YangMills.SUSY.finiteBerezinWeighted_topWeight_basis_empty_of_pos
#print axioms YangMills.SUSY.finiteBerezinWeighted_topWeight_basis_of_nonempty
#print axioms YangMills.SUSY.finiteBerezinWeighted_topWeight_top_basis_of_pos
#print axioms YangMills.SUSY.finiteBerezinWeighted_topWeight_basis_of_nonempty_ne_top
#print axioms YangMills.SUSY.finiteBerezinWeighted_topWeight_eq_top_add_empty_of_pos
#print axioms YangMills.SUSY.finiteBerezinWeighted_topWeight_apply_eq_top_add_empty_of_pos
#print axioms YangMills.SUSY.finiteBerezinWeighted_topWeight_sum_basis_eq_coeffs_of_pos
#print axioms YangMills.SUSY.finiteBerezinWeighted_topWeight_basis_mul_of_not_disjoint
#print axioms YangMills.SUSY.finiteBerezinWeighted_topWeight_powersetCard_mul_of_disjoint_top_of_pos
#print axioms YangMills.SUSY.finiteBerezinWeighted_topWeight_powersetCard_mul_of_disjoint_nonempty_ne_top
#print axioms YangMills.SUSY.finiteBerezinWeighted_basis_mul_of_not_disjoint
#print axioms YangMills.SUSY.finiteBerezinWeighted_sum_basis_mul_sum_basis
#print axioms YangMills.SUSY.finiteBerezinWeighted_sum_basis_mul_sum_basis_filter_disjoint
#print axioms YangMills.SUSY.finiteBerezinWeighted_topWeight_sum_basis_mul_sum_basis_filter_disjoint
#print axioms YangMills.SUSY.finiteExteriorBasis_singleton_mul_self
#print axioms YangMills.SUSY.finiteBerezin_expect_Q_eq_zero
#print axioms YangMills.SUSY.finiteBerezin_eq_expect_remainder_of_exactWard
#print axioms YangMills.SUSY.finiteBerezinWeighted_expect_Q_eq_zero
#print axioms YangMills.SUSY.finiteBerezinWeighted_eq_expect_remainder_of_exactWard
-- Ward-cancelled activities feeding the `Ω`-active skeleton-tail consumer.
#print axioms YangMills.SUSY.norm_finset_sum_expect_Q_le
#print axioms YangMills.SUSY.wardActivity_metric_bound_of_decomposition
#print axioms YangMills.SUSY.wardActivity_metric_bound_of_exact
#print axioms YangMills.SUSY.omegaClusterSkeletonRemainderSum_tsum_le_of_ward
#print axioms YangMills.SUSY.omegaClusterSkeletonRemainderSum_tsum_le_of_exact_ward

/-! ### The polymer modified metric (bricks P2b-i and P2b-ii) -/
#print axioms YangMills.RG.walk_crosses_frontier
#print axioms YangMills.RG.absorbedHole_touches_skeleton_single
#print axioms YangMills.RG.absorbedHole_touches_skeleton_multi
#print axioms YangMills.RG.touchingHoles_card_le
#print axioms YangMills.RG.card_le_activeEdges_add_one
#print axioms YangMills.RG.discreteModifiedMetric
#print axioms YangMills.RG.skeleton_card_le_discreteModifiedMetric_add_one
#print axioms YangMills.RG.discreteModifiedMetric_empty_holes
#print axioms YangMills.RG.fillings_card_le_two_pow
#print axioms YangMills.RG.cube_fillings_card_le_two_pow
#print axioms YangMills.RG.discreteModifiedMetric_le_bulkTreeLength
#print axioms YangMills.RG.discreteModifiedMetric_mono_skeleton
#print axioms YangMills.RG.discreteModifiedMetric_mono_holes
#print axioms YangMills.RG.skeleton_fillings_weight_summable
#print axioms YangMills.RG.discreteModifiedMetric_weight_summable
#print axioms YangMills.RG.holePolymerSystem
#print axioms YangMills.RG.omegaHolePolymerSystem
#print axioms YangMills.RG.omegaHolePolymerSystem_incomp_iff
#print axioms YangMills.RG.omegaHolePolymerSystem_incomp_iff_exists
#print axioms YangMills.RG.discreteModifiedMetric_singleton_skeleton
#print axioms YangMills.RG.discreteModifiedMetric_weight_summable_zero
#print axioms YangMills.RG.discreteModifiedMetric_d_zero
#print axioms YangMills.RG.discreteModifiedMetric_L_one
#print axioms YangMills.RG.holePolymerSystem_KPCriterion
#print axioms YangMills.RG.holePolymerSystem_converges
#print axioms YangMills.RG.holePolymerSystem_norm_clusterSum_le
#print axioms YangMills.RG.discreteModifiedMetric_empty_skeleton
#print axioms YangMills.RG.discreteModifiedMetric_d_one_empty_holes

#print axioms YangMills.RG.translateFinset
#print axioms YangMills.RG.skeleton_translate
#print axioms YangMills.RG.cubeConnected_translate
#print axioms YangMills.RG.polymerWithHoles_translate
#print axioms YangMills.RG.discreteModifiedMetric_translate
#print axioms YangMills.RG.translatePolymer
#print axioms YangMills.RG.holePolymerSystem_incomp_translate
#print axioms YangMills.RG.translateActivity
#print axioms YangMills.RG.rootedHolePolymerSum_translate

#print axioms YangMills.RG.closedNeigh
#print axioms YangMills.RG.closedNeigh_card_le
#print axioms YangMills.RG.incomp_imp_intersect
#print axioms YangMills.RG.holePolymerSystem_KPCriterion_volumeUniform
#print axioms YangMills.RG.holePolymerSystem_KPCriterion_volumeUniform_scaled
#print axioms YangMills.RG.holePolymerSystem_KPCriterion_volumeUniform_exp
#print axioms YangMills.RG.holePolymerSystem_converges_volumeUniform
#print axioms YangMills.RG.holePolymerSystem_norm_clusterSum_le_volumeUniform
#print axioms YangMills.RG.holePolymerSystem_converges_volumeUniform_scaled
#print axioms YangMills.RG.holePolymerSystem_norm_clusterSum_le_volumeUniform_scaled
#print axioms YangMills.RG.holePolymerSystem_converges_volumeUniform_exp
#print axioms YangMills.RG.holePolymerSystem_norm_clusterSum_le_volumeUniform_exp
#print axioms YangMills.RG.omega_filter_incomp_subset_skeleton
#print axioms YangMills.RG.omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton
#print axioms YangMills.RG.omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_scaled
#print axioms YangMills.RG.omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp
#print axioms YangMills.RG.omegaHolePolymerSystem_converges_volumeUniform_skeleton
#print axioms YangMills.RG.omegaHolePolymerSystem_norm_clusterSum_le_volumeUniform_skeleton
#print axioms YangMills.RG.omegaHolePolymerSystem_converges_volumeUniform_skeleton_exp
#print axioms YangMills.RG.omegaHolePolymerSystem_norm_clusterSum_le_volumeUniform_skeleton_exp
#print axioms YangMills.RG.omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp_of_metric_bound
#print axioms YangMills.RG.omegaHolePolymerSystem_converges_volumeUniform_skeleton_exp_of_metric_bound
#print axioms YangMills.RG.omegaHolePolymerSystem_norm_clusterSum_le_volumeUniform_skeleton_exp_of_metric_bound

#print axioms YangMills.RG.clusterUnion
#print axioms YangMills.RG.polymerWithHoles_biUnion
#print axioms YangMills.RG.clusterUnion_polymerWithHoles
#print axioms YangMills.RG.clusterUnion_nonempty
#print axioms YangMills.RG.clusterUnionPolymer
#print axioms YangMills.RG.clusterModifiedMetric
#print axioms YangMills.RG.clusterUnion_skeleton
#print axioms YangMills.RG.clusterUnion_fin_one
#print axioms YangMills.RG.clusterModifiedMetric_fin_one
#print axioms YangMills.RG.clusterDecayWeight
#print axioms YangMills.RG.clusterDecayWeight_fin_one
#print axioms YangMills.RG.walkConnected_union
#print axioms YangMills.RG.walk_union_connected
#print axioms YangMills.RG.clusterUnion_skeleton_card_le_clusterModifiedMetric_add_one
#print axioms YangMills.RG.cluster_closedNeigh_union_connected
#print axioms YangMills.RG.clusterRemainderSum_summable
#print axioms YangMills.RG.clusterRemainderSum_term_le_tilt
#print axioms YangMills.RG.clusterRemainderSum_summable_of_local
#print axioms YangMills.RG.clusterRemainderSum_tsum_le
#print axioms YangMills.RG.clusterRemainderSum_tsum_le_of_local
#print axioms YangMills.RG.clusterSkeletonRemainderSumTerm
#print axioms YangMills.RG.clusterSkeletonRemainderSumTerm_le
#print axioms YangMills.RG.clusterSkeletonRemainderSum_term_le_pinned
#print axioms YangMills.RG.clusterSkeletonRemainderSum_term_le_skeletonPinned
#print axioms YangMills.RG.clusterSkeletonRemainderSum_term_le_tilt
#print axioms YangMills.RG.clusterSkeletonRemainderSum_summable
#print axioms YangMills.RG.clusterSkeletonRemainderSum_tsum_le
#print axioms YangMills.RG.clusterSkeletonRemainderSum_summable_of_local
#print axioms YangMills.RG.clusterSkeletonRemainderSum_tsum_le_of_local
#print axioms YangMills.RG.clusterSkeletonRemainderSum_tsum_le_metric_bound
#print axioms YangMills.RG.clusterSkeletonRemainderSum_tsum_le_metric_bound_of_local
#print axioms YangMills.RG.clusterSkeletonRemainderSum_tsum_le_metric_bound_of_raw_local_metric
#print axioms YangMills.RG.omegaClusterSkeletonRemainderSumTerm
#print axioms YangMills.RG.omegaClusterSkeletonRemainderSum_term_le_skeletonPinned
#print axioms YangMills.RG.omegaClusterSkeletonRemainderSum_tsum_le
#print axioms YangMills.RG.omegaClusterSkeletonRemainderSum_summable_of_local
#print axioms YangMills.RG.omegaClusterSkeletonRemainderSum_tsum_le_of_local
#print axioms YangMills.RG.omegaClusterSkeletonRemainderSum_summable_of_uniform_local
#print axioms YangMills.RG.omegaClusterSkeletonRemainderSum_tsum_le_of_uniform_local
#print axioms YangMills.RG.omegaClusterSkeletonRemainderSum_tsum_le_metric_bound
#print axioms YangMills.RG.discreteModifiedMetric_le_clusterModifiedMetric

/-! ### Appendix-F exact finite-cover compiler, equations (639)--(640) -/
#print axioms YangMills.RG.confinedComponents_injective
#print axioms YangMills.RG.prod_confinedComponents_eq_prod
#print axioms YangMills.RG.appendixFCanonicalComponents_omegaSupport_disjoint
#print axioms YangMills.RG.sum_powerset_eq_sum_appendixFCanonicalCoverFamilies
#print axioms YangMills.RG.complex_exp_sum_eq_sum_powerset_rawMayer
#print axioms YangMills.RG.exp_finsetSum_eq_sum_powerset_prod_confinedOmegaComponents
#print axioms YangMills.RG.appendixF_finite_cover_expansion
#print axioms YangMills.RG.sum_connectedCovers_eq_sum_appendixFConnectedActivity
#print axioms YangMills.RG.appendixFConnectedActivity_congr
#print axioms YangMills.RG.appendixFTargetPolymerSystem_partition_eq_sum_admissibleTargetFamilies
#print axioms YangMills.RG.sum_admissibleTargetFamilies_prod_connectedMayerActivity_eq_sum_targetChoices
#print axioms YangMills.RG.appendixFTargetChoiceCoverFamily_mem_admissible
#print axioms YangMills.RG.appendixFCoverFamilyWeight_targetChoiceCoverFamily_eq
#print axioms YangMills.RG.appendixFTargetChoiceCoverFamily_image_coverUnion_eq
#print axioms YangMills.RG.appendixFConnectedCoverFamilyTargetChoiceSigma_targetChoiceCoverFamily_eq
#print axioms YangMills.RG.sum_appendixFAdmissibleTargetChoices_eq_sum_admissibleConnectedCoverFamilies
#print axioms YangMills.RG.sum_admissibleTargetFamilies_prod_connectedMayerActivity_eq_sum_admissibleConnectedCoverFamilies
#print axioms YangMills.RG.image_coverUnion_mem_appendixFAdmissibleTargetFamilies
#print axioms YangMills.RG.appendixFCoverUnion_injective_on_admissibleConnectedCoverFamily
#print axioms YangMills.RG.appendixFConnectedCoverFamilyTargetChoiceSigma_mem_choices
#print axioms YangMills.RG.appendixFTargetChoiceCoverFamily_connectedCoverFamilyTargetChoiceSigma_eq
#print axioms YangMills.RG.confinedComponent_eq_of_connected_no_exit
#print axioms YangMills.RG.appendixFCanonicalCoverFamilies_eq_admissibleConnectedCoverFamilies
#print axioms YangMills.RG.prod_one_add_eq_sum_appendixFAdmissibleConnectedCoverFamilies
#print axioms YangMills.RG.prod_one_add_eq_appendixFTargetPolymerSystem_partition
#print axioms YangMills.RG.complex_exp_sum_eq_appendixFTargetPolymerSystem_partition
-- two-support with-holes target geometry: skeleton compatibility and full-target injectivity
#print axioms YangMills.RG.appendixFHoleCoverUnion_skeleton
#print axioms YangMills.RG.appendixFHoleFullCoverUnion_nonempty
#print axioms YangMills.RG.appendixFHoleCoverUnion_cubeConnected
#print axioms YangMills.RG.appendixFHoleCoverUnion_polymerWithHoles
#print axioms YangMills.RG.appendixFHoleTargetRegion_cubeConnected
#print axioms YangMills.RG.appendixFHoleTargetRegion_polymerWithHoles
#print axioms YangMills.RG.appendixFHoleTargetRegion_skeleton_nonempty
#print axioms YangMills.RG.appendixFHoleTargetRegion_toOmegaPolymer
#print axioms YangMills.RG.appendixFHoleCoverUnion_injective_on_admissibleConnectedCoverFamily
#print axioms YangMills.RG.appendixFHoleCoverUnion_image_card_eq
#print axioms YangMills.RG.omegaOverlapGraph_univ_skeleton_adj_iff
#print axioms YangMills.RG.appendixFHoleConnectedActivity_congr
-- two-support with-holes target-family Fubini/lumping: active skeletons for
-- compatibility, full unions for target fibers.
#print axioms YangMills.RG.appendixFHoleTargetChoiceCoverFamily_mem_admissible
#print axioms YangMills.RG.appendixFHoleConnectedCoverFamilyTargetChoiceSigma_targetChoiceCoverFamily_eq
#print axioms YangMills.RG.sum_appendixFHoleAdmissibleTargetChoices_eq_sum_admissibleConnectedCoverFamilies
#print axioms YangMills.RG.sum_appendixFHoleAdmissibleTargetFamilies_prod_connectedMayerActivity_eq_sum_admissibleConnectedCoverFamilies
#print axioms YangMills.RG.prod_one_add_eq_sum_appendixFHoleAdmissibleTargetFamilies
#print axioms YangMills.RG.complex_exp_sum_eq_sum_appendixFHoleAdmissibleTargetFamilies
-- first integrated Appendix-F activity K#: local K(Y,ψ,φ), K#(Y,ψ), and norm inheritance.
#print axioms YangMills.RG.appendixFHoleConnectedLocalActivity_globalEval
#print axioms YangMills.RG.appendixFHoleConnectedLocalActivity_spectatorSupport_subset
#print axioms YangMills.RG.appendixFHoleConnectedLocalActivity_fluctuationSupport_subset
#print axioms YangMills.RG.appendixFHoleKsharp_globalEval
#print axioms YangMills.RG.norm_appendixFHoleKsharp_globalEval_le
#print axioms YangMills.RG.appendixFHoleKsharp_support_subset
-- n-ary ultralocal product-measure factorization and its Appendix-F K# adapters.
#print axioms YangMills.RG.LocalFunctional.integral_finsetProd_of_pairwise_disjoint_support
#print axioms YangMills.RG.LocalActivity.integral_finsetProd_of_pairwise_disjoint_fluctuationSupport
#print axioms YangMills.RG.appendixFHoleConnectedLocalActivity_fluctuationSupport_subset_skeleton
#print axioms YangMills.RG.appendixFHoleKsharp_pairwise_disjoint_support_of_admissibleTargetFamilies
#print axioms YangMills.RG.integral_prod_appendixFHoleConnectedLocalActivity_eq_prod_Ksharp_of_local_fluctuationSupport_subset_skeleton
#print axioms YangMills.RG.integral_prod_appendixFHoleKsharp_eq_prod_integral_of_admissibleTargetFamilies
#print axioms YangMills.RG.integral_sum_appendixFHoleConnectedLocalActivity_eq_sum_prod_Ksharp_of_local_fluctuationSupport_subset_skeleton
#print axioms YangMills.RG.integral_sum_appendixFHoleKsharp_eq_sum_prod_integral_of_admissibleTargetFamilies
-- finite quantitative first-activity majorant: raw exponential pointwise
-- decay implies a connected-cover metric sum, still before (641)--(642).
#print axioms YangMills.RG.norm_appendixFComponentWeight_expSubOne_le_metricProduct
#print axioms YangMills.RG.norm_appendixFConnectedActivity_le_metricProductCoverSum
#print axioms YangMills.RG.appendixF_metricProduct_eq_metricCoverWeight
#print axioms YangMills.RG.norm_appendixFConnectedActivity_le_metricCoverSum
#print axioms YangMills.RG.norm_appendixFHoleConnectedMayerActivity_expSubOne_le_metricCoverSum
-- finite localization: a target-fiber cover sum is bounded by any pinned
-- connected-cover sum through a site/cube of the target.
#print axioms YangMills.RG.appendixFMetricCoverWeight_nonneg
#print axioms YangMills.RG.appendixFTargetMetricCoverSum_le_pinnedMetricCoverSum
#print axioms YangMills.RG.norm_appendixFConnectedActivity_le_pinnedMetricCoverSum
#print axioms YangMills.RG.appendixFHoleTargetMetricCoverSum_le_pinnedMetricCoverSum
#print axioms YangMills.RG.norm_appendixFHoleConnectedMayerActivity_expSubOne_le_pinnedMetricCoverSum
-- finite with-holes modified-metric stitching: the geometric part of (641),
-- still before connected-cover entropy and the activity bound (642).
#print axioms YangMills.RG.discreteModifiedMetric_add_one_le_card_of_spanning_set
#print axioms YangMills.RG.appendixFHoleCoverUnion_discreteModifiedMetric_add_one_le_sum
#print axioms YangMills.RG.appendixFHoleTargetFiber_discreteModifiedMetric_add_one_le_sum
-- finite target-fiber entropy: forget connectedness/exact-union constraints,
-- overcount by a nonempty powerset, and absorb into exp(sum)-1.
#print axioms YangMills.RG.skeleton_mono_of_subset
#print axioms YangMills.RG.appendixFTargetFiber_subset_nonemptyPowerset
#print axioms YangMills.RG.sum_powerset_erase_empty_prod_le_exp_sub_one
#print axioms YangMills.RG.appendixFTargetFiber_prod_le_exp_sub_one
-- local modified-metric summability adapters before the first K# estimate.
#print axioms YangMills.RG.appendixFHole_rootedFiniteExpWeightSum_le
#print axioms YangMills.RG.appendixFHole_containedWeightSum_le_metric_mul_of_rooted
-- source-shaped exact first K(Y)/K# estimate before second-gas residual losses.
#print axioms YangMills.RG.norm_appendixFHoleConnectedLocalActivity_globalEval_le_expSubOne
#print axioms YangMills.RG.norm_appendixFHoleKsharp_globalEval_le_expSubOne_of_rawMetricDecay
#print axioms YangMills.RG.norm_appendixFHoleKsharp_globalEval_le_expSubOne_of_rawMetricDecay_rooted
-- second Appendix-F hard-core gas from evaluated K#: structural only, with KP
-- exposed as a pointwise majorant hypothesis rather than as Dimock (642).
#print axioms YangMills.RG.appendixFHoleSecondGas_activity
#print axioms YangMills.RG.appendixFHoleSecondGasActivity_eq_zero_of_not_mem_targetRegion
#print axioms YangMills.RG.appendixFHoleSecondGas_KPCriterion_of_majorant
-- spectator-integrated scalar K# normalization: structural bridge from the
-- finite K# target-family identity to the scalar zK family used by H#.
#print axioms YangMills.RG.appendixFHoleIntegratedKsharpActivity_eq_integral
#print axioms YangMills.RG.appendixFHoleIntegratedKsharpActivity_eq_zero_of_not_mem_targetRegion
#print axioms YangMills.RG.appendixFHoleIntegratedSecondGas_activity
#print axioms YangMills.RG.integral_sum_appendixFHoleKsharp_eq_sum_prod_integratedKsharpActivity_of_admissibleTargetFamilies
-- second Ursell object H#: finite union-fiber bookkeeping only; no convergence
-- or residual estimate is hidden in the totalized `tsum` definition.
#print axioms YangMills.RG.appendixFHoleHsharpTerm_eq_sum_filter
#print axioms YangMills.RG.appendixFHoleHsharpTerm_eq_zero_of_no_union
#print axioms YangMills.RG.sum_appendixFHoleHsharpTerm_eq_clusterSum_term
#print axioms YangMills.RG.appendixFHoleHsharpOfKsharp_eq
#print axioms YangMills.RG.appendixFHoleHsharpOfIntegratedKsharp_eq
-- residual H# adapter: source complex-norm estimates feed the real
-- omega-rooted UV-decay producer without hiding Dimock's analytic bound.
#print axioms YangMills.RG.complex_re_contracts_norm
#print axioms YangMills.RG.complex_im_contracts_norm
#print axioms YangMills.RG.clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharp_le
#print axioms YangMills.RG.rooted_clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharp_le
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_four_mul_margin
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_im
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_im_four_mul_margin
-- finite partial H# truncations: no convergence of the outer tsum is used.
#print axioms YangMills.RG.appendixFHoleHsharpPartial_zero
#print axioms YangMills.RG.appendixFHoleHsharpPartial_succ
#print axioms YangMills.RG.sum_appendixFHoleHsharpPartial_eq_sum_clusterSum_terms
#print axioms YangMills.RG.clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharpPartial_le
#print axioms YangMills.RG.rooted_clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharpPartial_le
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharpPartial
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharpPartial_four_mul_margin
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharpPartial_re
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharpPartial_re_four_mul_margin
-- convergence interface: fixed-target summability + uniform partial bounds.
#print axioms YangMills.RG.appendixFHoleHsharpPartial_tendsto
#print axioms YangMills.RG.appendixFHoleHsharp_eq_partial_add_tail
#print axioms YangMills.RG.appendixFHoleHsharp_sub_partial_tendsto_zero
#print axioms YangMills.RG.norm_appendixFHoleHsharp_sub_partial_le_tail_norm_tsum
#print axioms YangMills.RG.norm_appendixFHoleHsharp_sub_partial_le_of_tail_norm_bound
#print axioms YangMills.RG.norm_appendixFHoleHsharp_le_of_partial_bound
#print axioms YangMills.RG.clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharpPartial_limit_le
#print axioms YangMills.RG.rooted_clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharpPartial_limit_le
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_of_partial_bounds
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_of_partial_bounds_four_mul_margin
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_of_partial_bounds
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_of_partial_bounds_four_mul_margin
-- pointwise limit interface: explicit convergence hypotheses transfer
-- finite-cutoff residual estimates before the rooted polymer tsum is used.
#print axioms YangMills.RG.tendsto_appendixFHoleHsharpPartial_of_summable
#print axioms YangMills.RG.norm_appendixFHoleHsharp_le_residual_of_partial_limit
#print axioms YangMills.RG.norm_appendixFHoleHsharp_le_residual_of_summable_terms
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_partial_limit
-- termwise second-Ursell majorant interface: summable majorants supply
-- fixed-target summability, finite-partial residual bounds, and tails.
#print axioms YangMills.RG.norm_appendixFHoleHsharpTerm_le_clusterWeight
#print axioms YangMills.RG.summable_appendixFHoleHsharpTerm_of_norm_le_majorant
#print axioms YangMills.RG.summable_appendixFHoleHsharpTerm_of_sizeMajorant
#print axioms YangMills.RG.summable_appendixFHoleHsharpTerm_of_KPCriterion
#print axioms YangMills.RG.norm_appendixFHoleHsharpPartial_le_majorant_sum
#print axioms YangMills.RG.appendixFHoleHsharp_tail_norm_tsum_le_majorant_tail
#print axioms YangMills.RG.norm_appendixFHoleHsharp_sub_partial_le_majorant_tail
#print axioms YangMills.RG.norm_appendixFHoleHsharpPartial_le_residual_of_sizeMajorant
#print axioms YangMills.RG.norm_appendixFHoleHsharp_le_residual_of_term_majorant
#print axioms YangMills.RG.norm_appendixFHoleHsharp_le_residual_of_sizeMajorant
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_term_majorant
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_sizeMajorant
-- closed-form geometric second-Ursell majorants: A*q^n supplies the
-- summability, finite-partial, shifted-tail, and residual bookkeeping.
#print axioms YangMills.RG.sum_range_le_tsum_of_nonneg
#print axioms YangMills.RG.summable_geometric_majorant
#print axioms YangMills.RG.tsum_geometric_majorant
#print axioms YangMills.RG.sum_range_geometric_majorant_le_closed
#print axioms YangMills.RG.tsum_geometric_majorant_tail
#print axioms YangMills.RG.norm_appendixFHoleHsharp_sub_partial_le_geometric_tail
#print axioms YangMills.RG.norm_appendixFHoleHsharp_le_residual_of_geometric_term_majorant
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_geometric_term_majorant
-- source-facing absolute H# majorants: a finite nonnegative union-fiber term
-- is the explicit source object feeding the geometric consumers.
#print axioms YangMills.RG.norm_appendixFHoleHsharpTerm_le_absTerm
#print axioms YangMills.RG.appendixFHsharpSourceMajorant_of_absTerm_geometric
#print axioms YangMills.RG.appendixFHsharpSourceMajorant_of_factorized_absTerm_geometric
#print axioms YangMills.RG.appendixFHoleIntegratedKsharpActivityFamily_eq
#print axioms YangMills.RG.appendixFHsharpSourceMajorant_of_integratedKsharp_absTerm_geometric
#print axioms YangMills.RG.appendixFHsharpSourceMajorant_of_integratedKsharp_factorized_absTerm_geometric
#print axioms YangMills.RG.norm_appendixFHoleHsharpOfIntegratedKsharp_le_residual_of_source_majorant
#print axioms YangMills.RG.AppendixFHsharpSourceMajorant.summable_terms
#print axioms YangMills.RG.AppendixFHsharpSourceMajorant.tail_bound
#print axioms YangMills.RG.AppendixFHsharpSourceMajorant.residual_bound
#print axioms YangMills.RG.norm_appendixFHoleHsharp_le_residual_of_source_majorant
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_source_majorant
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharpOfIntegratedKsharp_re_four_mul_margin_of_source_majorant
-- finite tree majorant for the exact fixed-union absolute H# coefficient.
#print axioms YangMills.RG.appendixFHoleHsharpTreeTerm
#print axioms YangMills.RG.appendixFHoleHsharpAbsTerm_le_treeTerm
#print axioms YangMills.RG.appendixFHsharpSourceMajorant_of_treeTerm_geometric
#print axioms YangMills.RG.appendixFHsharpSourceMajorant_of_factorized_treeTerm_geometric
#print axioms YangMills.RG.appendixFHsharpSourceMajorant_of_integratedKsharp_treeTerm_geometric
#print axioms YangMills.RG.appendixFHsharpSourceMajorant_of_integratedKsharp_factorized_treeTerm_geometric
-- weighted finite tree transfer: extracts an activity-size epsilon^(n+1)
-- from the source-facing tree term and leaves a purely weighted tree sum.
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeTerm
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeTerm_nonneg
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeTerm_zero
#print axioms YangMills.RG.appendixFHoleHsharpTreeTerm_le_scaled_weightedTreeTerm
#print axioms YangMills.RG.appendixFHoleHsharpTreeTerm_le_factorized_of_weighted_bound
#print axioms YangMills.RG.appendixFHoleHsharpTreeTerm_le_factorized_of_weighted_geometric
#print axioms YangMills.RG.appendixFHoleHsharpMarkedSkeletonTreeTerm
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeTerm_le_markedSkeletonSum
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeTerm_le_markedSkeletonTreeTerm
#print axioms YangMills.RG.appendixFHoleHsharpMarkedSkeletonTreeTerm_le_markedIndexSum
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedIndexSum
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeTerm_le_markedIndexSum
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootSum
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootRawSum
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootChildOrderSum
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootSum_eq_inv_factorial_mul_rawSum
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootChildOrderSum_eq_childFactorSum
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum_le_inv_succ_mul_rawSum
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootChildOrderSum_le_inv_succ_mul_rawSum
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedIndexSum_eq_card_mul_root
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeTerm_le_card_mul_markedRootSum
-- finite second-Ursell geometry for the future weighted leaf summation:
-- target metric stitching, rooted hard-core sums, and factorial moments.
#print axioms YangMills.RG.omegaClusterUnion_discreteModifiedMetric_add_one_le_sum_of_spanningTree
#print axioms YangMills.RG.appendixFHole_incomp_expWeightSum_le_skeletonCard_mul
#print axioms YangMills.RG.appendixFHole_rootedFiniteMetricMomentExpWeightSum_le
#print axioms YangMills.RG.appendixFHole_containedMetricMomentExpWeightSum_le_metric_mul
#print axioms YangMills.RG.appendixFHole_incomp_expWeight_metricMomentSum_le_factorial_mul
-- source-facing cluster3 hole geometry: Ω as the active complement of holes
-- and the rooted local incompatibility contract consumed by Route A.
#print axioms YangMills.RG.skeleton_eq_inter_omegaRegion
#print axioms YangMills.RG.appendixFHole_incompatibleExpWeightSum_le_metric_mul_of_rooted
-- closed source-facing Dimock-II `cluster3` contract for H#.
#print axioms YangMills.RG.AppendixFHsharpCluster3Contract.of_unshifted_residual_bound
#print axioms YangMills.RG.AppendixFHsharpCluster3Contract.residual_bound
#print axioms YangMills.RG.norm_appendixFHoleHsharp_le_residual_of_cluster3_contract
#print axioms YangMills.RG.norm_appendixFHoleHsharpOfIntegratedKsharp_le_residual_of_cluster3_contract
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_cluster3_contract
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharpOfIntegratedKsharp_re_four_mul_margin_of_cluster3_contract
-- source-facing packaged geometric H# profiles: one record now supplies the
-- summability, tail, residual, and UV consumers without duplicating fields.
#print axioms YangMills.RG.AppendixFHsharpGeometricMajorantProfile.summable_terms
#print axioms YangMills.RG.AppendixFHsharpGeometricMajorantProfile.tail_bound
#print axioms YangMills.RG.AppendixFHsharpGeometricMajorantProfile.residual_bound
#print axioms YangMills.RG.AppendixFHsharpGeometricMajorantProfile.singleScaleUVDecay_of_profile
#print axioms YangMills.RG.balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_weighted_tree_geometric
#print axioms YangMills.RG.balabanCMP116AppendixFHsharpCluster3Contract_of_weighted_tree_geometric
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_weighted_tree_geometric

#print axioms YangMills.RG.Ubar_gaugeAct
#print axioms YangMills.RG.Ubar_locality

#print axioms YangMills.RG.scaleSpacing
#print axioms YangMills.RG.covUV_concrete
#print axioms YangMills.RG.hUV_of_per_scale

-- target F1: second moment trace norm-squared
#print axioms YangMills.ClayCore.sunHaarProb_trace_normSq_integral_eq_one
#print axioms YangMills.ClayCore.sunHaarProb_fundamental_entry_orthogonality
#print axioms YangMills.ClayCore.inner_fundamentalMatrixCoeffL2
#print axioms YangMills.ClayCore.orthonormal_normalizedFundamentalMatrixCoeffL2
#print axioms YangMills.ClayCore.ContinuousUnitaryMatrixRep.character_conj
#print axioms YangMills.ClayCore.ContinuousUnitaryMatrixRep.intertwiner_bijective_or_eq_zero
#print axioms YangMills.ClayCore.ContinuousUnitaryMatrixRep.exists_eq_smul_one_of_self_intertwiner
#print axioms YangMills.ClayCore.ContinuousUnitaryMatrixRep.haarAverageMatrix_mul_eq_mul_haarAverageMatrix
#print axioms YangMills.ClayCore.ContinuousUnitaryMatrixRep.haarAverageMatrix_eq_zero_of_not_equiv
#print axioms YangMills.ClayCore.ContinuousUnitaryMatrixRep.exists_haarAverageMatrix_eq_smul_one
#print axioms YangMills.ClayCore.ContinuousUnitaryMatrixRep.integral_matrixCoeff_mul_star_eq_zero_of_not_equiv
#print axioms YangMills.ClayCore.ContinuousUnitaryMatrixRep.trace_haarAverageMatrix
#print axioms YangMills.ClayCore.ContinuousUnitaryMatrixRep.haarAverageMatrix_eq_trace_div_card_smul_one
#print axioms YangMills.ClayCore.ContinuousUnitaryMatrixRep.integral_matrixCoeff_mul_star
#print axioms YangMills.ClayCore.ContinuousUnitaryMatrixRep.integral_character_mul_star_eq_zero_of_not_equiv
#print axioms YangMills.ClayCore.ContinuousUnitaryMatrixRep.integral_character_mul_star
#print axioms YangMills.ClayCore.ContinuousUnitaryMatrixRep.inner_characterL2_eq_zero_of_not_equiv
#print axioms YangMills.ClayCore.ContinuousUnitaryMatrixRep.inner_characterL2
#print axioms YangMills.ClayCore.ContinuousUnitaryMatrixRep.orthonormal_characterL2
#print axioms YangMills.ClayCore.ContinuousUnitaryMatrixRep.linearIndependent_characterL2
#print axioms YangMills.ClayCore.ContinuousUnitaryMatrixRep.inner_characterL2_sum
#print axioms YangMills.ClayCore.ContinuousUnitaryMatrixRep.characterL2_sum_eq_sum_iff
#print axioms YangMills.ClayCore.ContinuousUnitaryMatrixRep.characterL2_sum_eq_zero_iff
#print axioms YangMills.ClayCore.ContinuousUnitaryMatrixRep.inner_characterL2_sum_sum
#print axioms YangMills.ClayCore.ContinuousUnitaryMatrixRep.norm_sq_characterL2_sum
#print axioms YangMills.ClayCore.ContinuousUnitaryMatrixRep.norm_sq_characterL2_sum_sub_sum
