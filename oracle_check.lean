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
import YangMills.RG.RelativeBVRetraction
import YangMills.RG.PolymerSummabilityBridge
import YangMills.RG.AppendixFHsharp
import YangMills.RG.AppendixFHsharpResidual
import YangMills.RG.AppendixFHsharpPartial
import YangMills.RG.AppendixFHsharpConvergence
import YangMills.RG.AppendixFHsharpLimit
import YangMills.RG.AppendixFHsharpMajorant
import YangMills.RG.AppendixFHsharpGeometricMajorant
import YangMills.RG.AppendixFHsharpSourceMajorant
import YangMills.RG.AppendixFSecondUrsellSource
import YangMills.RG.AppendixFSecondUrsellLeafSummation
import YangMills.RG.AppendixFSecondUrsellClosure
import YangMills.RG.AppendixFCluster3Geometry
import YangMills.RG.AppendixFHsharpCluster3
import YangMills.RG.AppendixFHsharpProfile
import YangMills.RG.AppendixFHsharpMarkedVertexSource
import YangMills.RG.AppendixFHsharpLeafSource
import YangMills.Paper.GapRefinementChallenge
import YangMills.SUSY.ValenceCarry
import YangMills.SUSY.FiniteBerezin
import YangMills.SUSY.WardPolymer

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
#print axioms YangMills.wilsonLineSU_centerAct_val
#print axioms YangMills.integral_wilsonLineSU_entry_eq_zero
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
#print axioms YangMills.KP.tree_walk_bound_vertexwise
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
#print axioms YangMills.KP.prod_bfsParent_nonroot_eq_prod_pow_rootedChildCount
#print axioms YangMills.KP.card_rootedChildOrderAssignments
#print axioms YangMills.KP.prod_factorial_dvd_factorial_sum
#print axioms YangMills.KP.prod_factorial_le_factorial_sum
#print axioms YangMills.KP.rootedChildCount_factorialProduct_dvd_factorial
#print axioms YangMills.KP.rootedChildCount_factorialProduct_le_factorial
#print axioms YangMills.KP.rootedChildCount_factorialProduct_real_le_factorial
#print axioms YangMills.KP.rootedChildCount_factorialProduct_inv_succ_factorial_le_inv_succ
#print axioms YangMills.KP.parentMapProfileCount_eq_centralBinom
#print axioms YangMills.KP.parentMapProfileCount_le_four_pow
#print axioms YangMills.KP.sum_parentMapChildCount_factorialProduct_le_factorial_mul_profileCount
#print axioms YangMills.KP.sum_parentMapChildCount_factorialProduct_le_factorial_mul_centralBinom
#print axioms YangMills.KP.sum_parentMapChildCount_factorialProduct_le_factorial_mul_four_pow
#print axioms YangMills.KP.sum_rootedChildCount_factorialProduct_le_factorial_mul_profileCount
#print axioms YangMills.KP.sum_rootedChildCount_factorialProduct_le_factorial_mul_centralBinom
#print axioms YangMills.KP.sum_rootedChildCount_factorialProduct_le_factorial_mul_four_pow
#print axioms YangMills.KP.rootedChildCount_factorialTreeSum_normalized_le_centralBinom
#print axioms YangMills.KP.rootedChildCount_factorialTreeSum_normalized_le_four_pow

/-! ## The IR clustering bound and the correlator decay -/
#print axioms YangMills.truncated_correlation_bound
#print axioms YangMills.gibbs_truncated_correlation_bound
#print axioms YangMills.sun_two_plaquette_correlator_bound
-- interacting open Wilson-line matrix-coefficient selection:
#print axioms YangMills.integral_wilsonLineSU_entry_gibbs_eq_zero
-- mixed open Wilson-line coefficient with finite Wilson-loop products:
#print axioms YangMills.integral_wilsonLineSU_entry_mul_wilsonLoopSU_listProd_gibbs_eq_zero
-- connected mixed open Wilson-line coefficient with finite Wilson-loop products:
#print axioms YangMills.connected_wilsonLineSU_entry_mul_wilsonLoopSU_listProd_gibbs_eq_zero
-- starred mixed open Wilson-line coefficient with finite Wilson-loop products:
#print axioms YangMills.integral_wilsonLineSU_entry_mul_star_wilsonLoopSU_listProd_gibbs_eq_zero
#print axioms YangMills.connected_wilsonLineSU_entry_mul_star_wilsonLoopSU_listProd_gibbs_eq_zero
-- interacting centre-charge selection for the connected two-loop expression:
#print axioms YangMills.connected_wilsonLoopSU_gibbs_eq_zero
-- mixed charge selection for `W · conj W'` and its connected expression:
#print axioms YangMills.integral_wilsonLoopSU_mul_star_gibbs_eq_zero
#print axioms YangMills.connected_wilsonLoopSU_star_gibbs_eq_zero
-- finite-product centre-charge selection, including mixed holomorphic/conjugate products:
#print axioms YangMills.integral_wilsonLoopSU_listProd_gibbs_eq_zero
#print axioms YangMills.integral_wilsonLoopSU_listProd_star_gibbs_eq_zero
#print axioms YangMills.connected_wilsonLoopSU_listProd_star_gibbs_eq_zero
#print axioms YangMills.connected_wilsonLoopSU_listProd_gibbs_eq_zero
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
#print axioms YangMills.refinementsProduceArbitrarilySmallPositiveExcitations_of_not_hasUniformPositiveEnergyGap
#print axioms YangMills.not_hasUniformPositiveEnergyGap_iff_refinementsProduceArbitrarilySmallPositiveExcitations
#print axioms YangMills.hasUniformPositiveEnergyGap_hasStagewisePositiveEnergyGap
#print axioms YangMills.hasUniformPositiveEnergyGap_iff_exists_stagewise_gaps_boundedBelow
#print axioms YangMills.not_exists_stagewise_gaps_boundedBelow_of_refinementsProduceArbitrarilySmallPositiveExcitations
#print axioms YangMills.halfScaleExcitation_stagewise_but_not_uniform
#print axioms YangMills.halfScaleExcitation_no_stagewise_gaps_boundedBelow

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
#print axioms YangMills.RG.lattice_mass_gap_of_cluster_and_marginal_coupling_with_summable_exception
#print axioms YangMills.RG.lattice_mass_gap_of_cluster_and_marginal_coupling_split_exception
-- non-vacuity: the marginal-coupling recursion is satisfiable (logistic flow)
#print axioms YangMills.RG.exists_marginal_coupling_flow
-- semantic producer/consumer split: renormalized hole activities imply the
-- scalar single-scale UV decay consumed by the mass-gap assembly
#print axioms YangMills.RG.singleScaleUVDecay_of_renormalizedHoleActivities
#print axioms YangMills.RG.summable_abs_of_renormalizedHoleActivityDecay
#print axioms YangMills.RG.singleScaleUVDecay_of_renormalizedHoleActivities_summableWeight
#print axioms YangMills.RG.YMActivityErrorBudget.summable_abs_of_rawYMActivityDecay
#print axioms YangMills.RG.YMActivityErrorBudget.singleScaleUVDecay_of_rawYMActivityDecay_summableWeight
#print axioms YangMills.RG.YMActivityErrorBudget.RawYMActivityDecomposition.weight_nonneg
#print axioms YangMills.RG.YMActivityErrorBudget.RawYMActivityDecomposition.weight_tsum_nonneg
#print axioms YangMills.RG.YMActivityErrorBudget.RawYMActivityDecomposition.singleScaleUVDecay_of_tsum_summableWeight
#print axioms YangMills.RG.YMActivityErrorBudget.singleScaleUVDecay_of_sum_components_profile_tsum_summableWeight
#print axioms YangMills.RG.YMActivityErrorBudget.RawYMActivityDecomposition.lattice_mass_gap_marginal_of_tsum_summableWeight
#print axioms YangMills.RG.YMActivityErrorBudget.RawYMActivityDecomposition.lattice_mass_gap_marginal_of_tsum_summableWeight_of_bound
#print axioms YangMills.RG.YMActivityErrorBudget.lattice_mass_gap_marginal_of_sum_components_profile_tsum_summableWeight
#print axioms YangMills.RG.YMActivityErrorBudget.lattice_mass_gap_marginal_of_sum_components_profile_tsum_summableWeight_of_bound
#print axioms YangMills.RG.lattice_mass_gap_of_singleScaleUVDecay_geometric
-- relative BV/BRST retraction interface: exact/approximate cancellation
-- leaves only the lifted effective observable plus a boundary defect.
#print axioms YangMills.RG.RelativeBVOneStep.push_chain_apply
#print axioms YangMills.RG.RelativeBVOneStep.effective_closed_of_closed
#print axioms YangMills.RG.RelativeBVOneStep.relative_sdr_apply
#print axioms YangMills.RG.RelativeBVOneStep.expectation_defect_identity
#print axioms YangMills.RG.RelativeBVOneStep.expectation_defect_bound_of_approx_ward
#print axioms YangMills.RG.RelativeBVOneStep.expectation_defect_bound_of_rooted_obligations
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
#print axioms YangMills.RG.summable_abs_of_clusterWithHolesActivityDecay
#print axioms YangMills.RG.summable_abs_of_omegaRootedClusterWithHolesActivityDecay
#print axioms YangMills.RG.clusterWithHolesExpWeight_tsum_nonneg
#print axioms YangMills.RG.clusterWithHolesExpWeight_bound_nonneg
#print axioms YangMills.RG.singleScaleUVDecay_of_clusterWithHolesActivities
#print axioms YangMills.RG.lattice_mass_gap_marginal_of_clusterWithHolesActivities
#print axioms YangMills.RG.lattice_mass_gap_marginal_of_clusterWithHolesActivities_four_mul_margin
-- Appendix-F first/final rate normalization and canonical exponential-weight split.
#print axioms YangMills.RG.appendixFKsharpRate_eq_residual_add_leafRemainder
#print axioms YangMills.RG.appendixFKsharpRate_sub_left
#print axioms YangMills.RG.appendixFHoleExpWeight_add
#print axioms YangMills.RG.appendixFHoleExpWeight_ksharpRate_factor
#print axioms YangMills.RG.appendixFHoleExpWeight_antitone
#print axioms YangMills.RG.appendixFHoleExpWeight_leafRemainder_le
#print axioms YangMills.RG.appendixFHoleExpWeight_ksharpRate_le_residual_mul_leafBudget
-- residual summability interface: the source estimate itself is packaged
-- separately from either residual-rate or reference-`κ₀` geometric summability.
#print axioms YangMills.RG.ClusterExpansionWithHolesEstimate.residualRate_nonneg_of_three_mul_add_le
#print axioms YangMills.RG.ClusterExpansionWithHolesEstimate.finite_sum_abs_le_residualWeightSum
#print axioms YangMills.RG.ClusterExpansionWithHolesEstimate.abs_tsum_le_of_residual_summability
#print axioms YangMills.RG.ClusterExpansionWithHolesEstimate.residualRate_nonneg_and_abs_tsum_le_of_residual_summability
#print axioms YangMills.RG.ClusterExpansionWithHolesEstimate.abs_tsum_le_of_reference_summability
#print axioms YangMills.RG.ClusterExpansionWithHolesEstimate.abs_tsum_le_of_reference_summability_four_mul_margin
-- type-local support substrate for constructive Dimock F.1 activities
#print axioms YangMills.RG.LocalFunctional.globalEval_eq_of_agreeOn
#print axioms YangMills.RG.LocalFunctional.globalEval_finsetProd
#print axioms YangMills.RG.LocalActivity.globalEval_eq_of_agreeOn
#print axioms YangMills.RG.LocalActivity.globalEval_reindex
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
#print axioms YangMills.RG.Kpow_finiteRange
-- volume-uniform lattice exponential summability from a shell-growth bound
-- (discharges the recurring geometric hypothesis of the whole decay stack)
#print axioms YangMills.RG.lattice_exp_sum_le_of_shell
-- explicit closed-form constant S = C·(1−r·e^{−σ})⁻¹ for a bounded-degree lattice
#print axioms YangMills.RG.lattice_exp_sum_le_geometric
-- resolvent-first local precision layer and inverse-square-root scalar tails
#check YangMills.RG.LocalFiniteRangeResolventData
#print axioms YangMills.RG.LocalFiniteRangeResolventData.resolvent_expDecay
#print axioms YangMills.RG.LocalFiniteRangeResolventData.Kpow_finiteRange
#print axioms YangMills.RG.inverseSqrtCoefficientMajorant_summable
#print axioms YangMills.RG.inverseSqrtCoefficientMajorant_tail_le
#print axioms YangMills.RG.inverseSqrtBinomialCoeff_majorant
#print axioms YangMills.RG.inverseSqrtBinomialCoeff_tail_le
#print axioms YangMills.RG.LocalFiniteRangeResolventData.inverseSqrtKernelTruncation_finiteRange
#print axioms YangMills.RG.LocalFiniteRangeResolventData.inverseSqrtKernelRemainder_expDecay
#print axioms YangMills.RG.normalizedPrecisionContraction_nonneg
#print axioms YangMills.RG.normalizedPrecisionContraction_lt_one
#print axioms YangMills.RG.inv_one_sub_normalizedPrecisionContraction
#print axioms YangMills.RG.inverseSqrtBinomialCoeff_normalized_tail_le
#print axioms YangMills.RG.inverseSqrtBinomialCoeff_normalized_scaled_tail_le
#print axioms YangMills.RG.PhysicalLocalSPDInverseSqrtData.precision_coercive
#print axioms YangMills.RG.PhysicalLocalSPDInverseSqrtData.kernelMajorant_Kpow_finiteRange
#print axioms YangMills.RG.PhysicalLocalSPDInverseSqrtData.inverseSqrtKernelTruncation_finiteRange
#print axioms YangMills.RG.PhysicalLocalSPDPrecisionRootCertificate.toLocalizedCovarianceRootCertificate
-- Schur boundedness: row-sum + quadratic-form (covariance) bound ≤ a·S
#print axioms YangMills.RG.expDecay_finset_row_le
-- collar-separated cross interaction: ExpDecay + separation ε pays exp(-κ ε)
#print axioms YangMills.RG.expDecay_separated_finset_sum_le
#print axioms YangMills.RG.expDecay_quadratic_form_le
-- the full ℓ² Schur test: operator-norm bound ‖K‖op ≤ a·S
#print axioms YangMills.RG.expDecay_op_bilinear_le
-- scalar Schur-Catalan budget closure: base coercivity beats finite defects
#print axioms YangMills.RG.schurCatalanBudget
#print axioms YangMills.RG.quadraticBudget_sub_finset_le
#print axioms YangMills.RG.quadraticBudget_sub_finset_pos
#print axioms YangMills.RG.schurCatalan_lower_bound_of_finset_budget
#print axioms YangMills.RG.schurCatalan_coercive_of_finset_budget
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
-- gauge precision coercivity: block Poincare/Hodge + Q†Q mass bookkeeping
#print axioms YangMills.RG.coercive_add_adjointMass_of_blockPoincare
#print axioms YangMills.RG.coercive_add_qMassCLM_of_blockPoincare
#print axioms YangMills.RG.coercive_add_perturbation
-- operator-norm perturbation budgets for coercive continuous linear maps
#print axioms YangMills.RG.abs_inner_apply_le_opNorm_mul_norm_sq
#print axioms YangMills.RG.isCoercive_add_of_opNorm_le
#print axioms YangMills.RG.isCoercive_sub_of_opNorm_le
#print axioms YangMills.RG.isCoercive_sub_tsum_of_norm_budget
#print axioms YangMills.RG.isCoerciveCLM_qMassCLM_zero
#print axioms YangMills.RG.isCoerciveCLM_add_qMassCLM_of_blockPoincare
#print axioms YangMills.RG.isCoerciveCLM_gaugeFixedBasePrecision_of_blockPoincare
#print axioms YangMills.RG.isCoerciveCLM_gaugeFixedPrecision_of_blockPoincare_normBudget
#print axioms YangMills.RG.gaugeFixedPrecision_coerciveWithPositiveConstant
#print axioms YangMills.RG.isCoerciveCLM_qMass_sub_tsum_of_blockPoincare_normBudget
#print axioms YangMills.RG.qMass_sub_tsum_coerciveWithPositiveConstant_of_blockPoincare_normBudget
#print axioms YangMills.RG.isCoerciveCLM_sub_finset_of_schurCatalan_blockPoincare
#print axioms YangMills.RG.inner_sub_finset_pos_of_schurCatalan_blockPoincare
-- exact finite-dimensional covariance constructed from strict coercivity
#print axioms YangMills.RG.isCoerciveCLM_norm_lower_bound
#print axioms YangMills.RG.isCoerciveCLM_injective
#print axioms YangMills.RG.isCoerciveCLM_surjective
#print axioms YangMills.RG.covarianceOfIsCoerciveCLM_apply_precision
#print axioms YangMills.RG.precision_apply_covarianceOfIsCoerciveCLM
#print axioms YangMills.RG.covarianceOfIsCoerciveCLM_comp_precision
#print axioms YangMills.RG.precision_comp_covarianceOfIsCoerciveCLM
#print axioms YangMills.RG.norm_covarianceOfIsCoerciveCLM_le
#print axioms YangMills.RG.covarianceOfIsCoerciveCLM_psd
-- exact covariance assembled for the abstract gauge-fixed precision form
#print axioms YangMills.RG.covarianceOfGaugeFixedPrecisionCLM_comp_precision
#print axioms YangMills.RG.precision_comp_covarianceOfGaugeFixedPrecisionCLM
#print axioms YangMills.RG.norm_covarianceOfGaugeFixedPrecisionCLM_le
#print axioms YangMills.RG.covarianceOfGaugeFixedPrecisionCLM_psd
-- full-periodic physical gauge cochains with explicit background adjoint data
#print axioms YangMills.RG.SUNAdjointModel.ad_inv_comp
#print axioms YangMills.RG.fineLineSum_constant
#print axioms YangMills.RG.linAvg_constant
#print axioms YangMills.RG.orientedOneValue_reverse
#print axioms YangMills.RG.covariantD0CLM_apply
#print axioms YangMills.RG.covariantD1CLM_apply
#print axioms YangMills.FinBox.shift_bijective
#print axioms YangMills.FinBox.shiftBack_bijective
#print axioms YangMills.FinBox.sum_shift
#print axioms YangMills.FinBox.sum_shiftBack
#print axioms YangMills.FinBox.shift_shiftBack_comm
#print axioms YangMills.FinBox.iter_shift_apply_self
#print axioms YangMills.FinBox.iter_shift_apply_ne
#print axioms YangMills.FinBox.eq_default_of_shift_invariant
#print axioms YangMills.RG.gaugeFixingMass_nonnegative
#print axioms YangMills.RG.gaugeFixingMass_inner_right
#print axioms YangMills.RG.gaugeFixingMass_nonnegative_right
#print axioms YangMills.RG.backgroundGaugeHodgeK0_nonnegative
#print axioms YangMills.RG.backgroundGaugeHodgeK0_inner_right
#print axioms YangMills.RG.backgroundGaugeHodgeK0_nonnegative_right
#print axioms YangMills.RG.flatGaugeHodgeK0_inner
#print axioms YangMills.RG.flatGaugeHodgeK0_inner_right
#print axioms YangMills.RG.flatGaugeHodgeK0_nonnegative_right
#print axioms YangMills.RG.covariantD1CLM_trivial_apply
#print axioms YangMills.RG.gaugeConstraintQCLM_trivial_apply
#print axioms YangMills.RG.isFlatHarmonicOneCochain_curl_apply_eq_zero
#print axioms YangMills.RG.isFlatHarmonicOneCochain_divergence_apply_eq_zero
#print axioms YangMills.RG.isFlatHarmonicOneCochain_div_apply_eq_zero
#print axioms YangMills.RG.isFlatHarmonicOneCochain_iff_flatGaugeHodgeK0_inner_right_eq_zero
#print axioms YangMills.RG.isFlatHarmonicOneCochain_iff_flatGaugeHodgeK0_inner_eq_zero
#print axioms YangMills.RG.flatGaugeHodgeK0CLM_eq_zero_iff_isFlatHarmonicOneCochain
#print axioms YangMills.RG.flatBlockConstraintQCLM_apply
#print axioms YangMills.RG.mem_flatBlockConstraintSupport_of_mem_linAvgSupport
#print axioms YangMills.RG.flatBlockConstraintQCLM_congr_of_eqOn_support
#print axioms YangMills.RG.flatBlockConstraintQCLM_constant_apply
#print axioms YangMills.RG.flatBlockConstraintQCLM_constant
#print axioms YangMills.RG.flatBlockConstraintQCLM_constant_eq_zero_iff
#print axioms YangMills.RG.flatBlockConstraintQCLM_injective_on_constants
#print axioms YangMills.RG.covariantD1CLM_trivial_constantPhysicalGaugeOneCochain
#print axioms YangMills.RG.inner_constantPhysicalGaugeOneCochain_covariantD0CLM_trivial
#print axioms YangMills.RG.gaugeConstraintQCLM_trivial_constantPhysicalGaugeOneCochain
#print axioms YangMills.RG.isFlatHarmonicOneCochain_constantPhysicalGaugeOneCochain
#print axioms YangMills.RG.flatGaugeHodgeK0CLM_constantPhysicalGaugeOneCochain
#print axioms YangMills.RG.flatConstant_jointKernel_eq_zero_iff
#print axioms YangMills.RG.PeriodicCurlDivKernelClassified
#print axioms YangMills.RG.torusCurl_eq_plaquette
#print axioms YangMills.RG.torusCurl_self
#print axioms YangMills.RG.torusCurl_swap
#print axioms YangMills.RG.torusCurl_eq_zero_of_ordered_plaquettes
#print axioms YangMills.RG.torusForwardDiff_sum
#print axioms YangMills.RG.torusForwardDiff_torusBackwardDiff_comm
#print axioms YangMills.RG.sum_inner_torusBackwardDiff
#print axioms YangMills.RG.sum_inner_torusLaplacian_eq_neg_sum_norm_sq
#print axioms YangMills.RG.finiteTorusDirichletIdentity
#print axioms YangMills.RG.torusLaplacian_component_eq_forwardDiff_divergence
#print axioms YangMills.RG.torusLaplacian_component_eq_zero_of_curl_div_zero
#print axioms YangMills.RG.torusForwardDiff_eq_zero_of_laplacian_eq_zero
#print axioms YangMills.RG.eq_default_of_torusLaplacian_eq_zero
#print axioms YangMills.RG.torusForwardDiff_eq_zero_of_curl_div_zero
#print axioms YangMills.RG.periodicCurlDivKernelClassified
#print axioms YangMills.RG.periodicCurlDivKernelClassified_of_dirichlet
#print axioms YangMills.RG.PeriodicCurlDivKernelClassified.proof
#print axioms YangMills.RG.flatHarmonicKernelClassified_of_curl_div
#print axioms YangMills.RG.flatHarmonicKernelClassified
#print axioms YangMills.RG.flatHarmonic_eq_constantPhysicalGaugeOneCochain
#print axioms YangMills.RG.flatHarmonicKernel_eq_constantSector
#print axioms YangMills.RG.flatGaugeHodgeKernel_eq_constantSector
#print axioms YangMills.RG.flatJointKernel_trivial_of_harmonicClassification
#print axioms YangMills.RG.exists_sq_norm_le_sum_three_sq_of_jointKernel_trivial
#print axioms YangMills.RG.exists_flatGaugeHodgeBlockPoincare_of_jointKernel_trivial
#print axioms YangMills.RG.flatGaugeHodgeBlockPoincare_of_harmonicClassification
#print axioms YangMills.RG.flatCurlDivBlockPoincare_of_harmonicClassification
#print axioms YangMills.RG.exists_flatGaugeHodgePoincare_of_periodicCurlDivClassification
#print axioms YangMills.RG.exists_flatGaugeHodgePoincare
#print axioms YangMills.RG.flatGaugeFixedPrecision_coerciveWithPositiveConstant_of_flatPoincare
#print axioms YangMills.RG.exists_flatGaugeFixedPrecision_coerciveWithPositiveConstant
#print axioms YangMills.RG.flatGaugeFixedCovarianceCLM_comp_precision
#print axioms YangMills.RG.precision_comp_flatGaugeFixedCovarianceCLM
#print axioms YangMills.RG.norm_flatGaugeFixedCovarianceCLM_le
#print axioms YangMills.RG.flatGaugeFixedCovarianceCLM_psd
#print axioms YangMills.RG.physicalCovarianceKernelBound_of_exponential
#print axioms YangMills.RG.flatGaugeFixedLocalizedCovarianceCertificate_of_kernelBound
#print axioms YangMills.RG.physicalLocalizedCovarianceRootCertificate_of_source
#print axioms YangMills.RG.flatGaugeFixedLocalizedCovarianceRootCertificate_of_source
#print axioms YangMills.RG.physicalLocalizedGaussianActivityCertificate_of_source
#print axioms YangMills.RG.physicalGaugeRawActivityBound_of_localizedGaussianActivityCertificate
#print axioms YangMills.RG.physicalGaugeSpectatorSupport_subset_of_localizedGaussianActivityCertificate
#print axioms YangMills.RG.physicalGaugeFluctuationSupport_subset_of_localizedGaussianActivityCertificate
#print axioms YangMills.RG.physicalGaugeAmplitude_nonneg_of_localizedGaussianActivityCertificate
#print axioms YangMills.RG.physicalGaugeWeight_nonneg_of_localizedGaussianActivityCertificate
#print axioms YangMills.RG.physicalGaugeActivityDecay_of_localizedGaussianActivityCertificate
#print axioms YangMills.RG.physicalGaugeRawActivityDecay_of_localizedGaussianActivityCertificate
#print axioms YangMills.RG.PhysicalGaugeCMP116ActivityAdapter.globalEval_activity
#print axioms YangMills.RG.PhysicalGaugeCMP116ActivityAdapter.spectatorSupport_activity_subset_activeSupport
#print axioms YangMills.RG.PhysicalGaugeCMP116ActivityAdapter.fluctuationSupport_activity_subset_activeSupport
#print axioms YangMills.RG.PhysicalGaugeCMP116ActivityAdapter.ofDictionary
#print axioms YangMills.RG.PhysicalGaugeCMP116ActivityAdapter.pullFluctuation_ofDictionary
#print axioms YangMills.RG.PhysicalGaugeCMP116ActivityAdapter.globalEval_activity_ofDictionary
#print axioms YangMills.RG.PhysicalGaugeCMP116ActivityAdapter.spectatorSupport_activity_ofDictionary_subset_iff
#print axioms YangMills.RG.PhysicalGaugeCMP116ActivityAdapter.fluctuationSupport_activity_ofDictionary_subset_iff
#print axioms YangMills.RG.PhysicalGaugeCMP116ActivityAdapter.activeSupport_ofDictionary_subset_iff
#print axioms YangMills.RG.PhysicalGaugeCMP116ActivityAdapter.localizedFamilyOfDictionary
#print axioms YangMills.RG.PhysicalGaugeCMP116ActivityAdapter.localizedFamilyOfDictionary_Omega
#print axioms YangMills.RG.PhysicalGaugeCMP116ActivityAdapter.localizedFamilyOfDictionary_activeSupport
#print axioms YangMills.RG.PhysicalGaugeCMP116ActivityAdapter.localizedFamilyOfDictionary_activity
#print axioms YangMills.RG.PhysicalGaugeCMP116ActivityAdapter.appendixFSupportHypotheses_of_localizedFamilyOfDictionary
#print axioms YangMills.RG.finBox_one_eq_iterShift
#print axioms YangMills.RG.constant_of_shift_invariant_finBox_one
#print axioms YangMills.RG.flatHarmonicKernelClassified_one
#print axioms YangMills.RG.flatGaugeHodgeBlockPoincare_one
#print axioms YangMills.RG.flatCurlDivBlockPoincare_one
#print axioms YangMills.RG.norm_sq_constantPhysicalGaugeOneCochain
#print axioms YangMills.RG.flatBlockConstraintQCLM_constant_norm_sq
#print axioms YangMills.RG.flatBlockConstraint_controls_constantSector
#print axioms YangMills.RG.flatGaugeHodgePoincare_constantSector_lower_bound
-- full-periodic flat Hodge/block-Poincare interface; source estimate remains external
#print axioms YangMills.RG.flatGaugeHodgePoincare
-- finite physical gauge-operator interface and soft full-space precision shell
#print axioms YangMills.RG.flatD1FullCLM_comp_flatD0FullCLM
#print axioms YangMills.RG.flatKslice_nonnegative
#print axioms YangMills.RG.positiveScaledLinAvgCLM_apply
#print axioms YangMills.RG.physicalPrecision_eq_flat_sub_defect
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
-- Cohomological valence carry: closed-shell contraction leaves only valence.
#print axioms YangMills.SUSY.ValenceCarryComplex.contracting_apply
#print axioms YangMills.SUSY.ValenceCarryComplex.Q_Q_apply
#print axioms YangMills.SUSY.ValenceCarryComplex.decomposition_of_closed
#print axioms YangMills.SUSY.ValenceCarryComplex.expect_eq_expect_valence_of_closed
#print axioms YangMills.SUSY.ValenceCarryComplex.expect_eq_zero_of_closedShell
#print axioms YangMills.SUSY.ValenceCarryComplex.expect_eq_expect_singlet_valence_of_closed
#print axioms YangMills.SUSY.ValenceCarryComplex.norm_expect_sub_expect_valence_le
#print axioms YangMills.SUSY.ValenceCarryComplex.expect_norm_le_of_valence_bound
#print axioms YangMills.SUSY.ValenceCarryComplex.expect_norm_le_of_valence_bound_approx
#print axioms YangMills.SUSY.ValenceCarryComplex.expect_norm_le_of_rooted_obligations
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
#print axioms YangMills.SUSY.mayerProduct_decomp_eq_sum_powerset
#print axioms YangMills.SUSY.mayerProduct_sub_base_eq_sum_powerset_erase_empty
#print axioms YangMills.SUSY.mem_mayerProduct_defectSubsets_iff
#print axioms YangMills.SUSY.mayerProduct_defectSupport_subset
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
#print axioms YangMills.RG.clusterUnion_component_subset
#print axioms YangMills.RG.clusterUnion_component_subset_of_eq
#print axioms YangMills.RG.clusterUnionPolymer
#print axioms YangMills.RG.clusterModifiedMetric
#print axioms YangMills.RG.clusterUnion_skeleton
#print axioms YangMills.RG.clusterUnion_component_skeleton_subset
#print axioms YangMills.RG.clusterUnion_component_skeleton_subset_of_eq
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
#print axioms YangMills.RG.appendixFCoverUnion_card_le_sum
#print axioms YangMills.RG.appendixFCoverUnion_card_real_le_sum
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
#print axioms YangMills.RG.appendixFHoleConnectedLocalActivity_globalEval_stronglyMeasurable
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
#print axioms YangMills.RG.appendixFHoleCoverUnion_card_le_metricSum_of_source_card_le_metric
#print axioms YangMills.RG.appendixFHoleTargetFiber_card_le_metricSum_of_source_card_le_metric
#print axioms YangMills.RG.appendixFHoleMetricCoverWeight_mul_exp_card_le_shifted_of_source_card_le_metric
-- finite target-fiber entropy: forget connectedness/exact-union constraints,
-- overcount by a nonempty powerset, and absorb into exp(sum)-1.
#print axioms YangMills.RG.skeleton_mono_of_subset
#print axioms YangMills.RG.appendixFTargetFiber_subset_nonemptyPowerset
#print axioms YangMills.RG.sum_powerset_erase_empty_prod_le_exp_sub_one
#print axioms YangMills.RG.appendixFTargetFiber_prod_le_exp_sub_one
-- local modified-metric summability adapters before the first K# estimate.
#print axioms YangMills.RG.appendixFHoleExpWeight_tilted_profile_le_of_card_le_metric
#print axioms YangMills.RG.appendixFHole_rootedFiniteExpWeightSum_le
#print axioms YangMills.RG.appendixFHole_containedWeightSum_le_metric_mul_of_rooted
-- source-shaped exact first K(Y)/K# estimate before second-gas residual losses.
#print axioms YangMills.RG.norm_appendixFHoleConnectedLocalActivity_globalEval_le_expSubOne
#print axioms YangMills.RG.norm_appendixFHoleKsharp_globalEval_le_expSubOne_of_rawMetricDecay
#print axioms YangMills.RG.integrable_appendixFHoleConnectedLocalActivity_globalEval_of_rawMetricDecay
#print axioms YangMills.RG.integrable_appendixFHoleConnectedLocalActivity_globalEval_of_rawMetricDecay_of_stronglyMeasurable
#print axioms YangMills.RG.integrable_appendixFHoleConnectedLocalActivity_globalEval_of_rawMetricDecay_of_factor_stronglyMeasurable
#print axioms YangMills.RG.norm_appendixFHoleKsharp_globalEval_le_expSubOne_of_rawMetricDecay_rooted
#print axioms YangMills.RG.integrable_appendixFHoleConnectedLocalActivity_globalEval_of_rawMetricDecay_rooted
#print axioms YangMills.RG.integrable_appendixFHoleConnectedLocalActivity_globalEval_of_rawMetricDecay_rooted_of_stronglyMeasurable
#print axioms YangMills.RG.integrable_appendixFHoleConnectedLocalActivity_globalEval_of_rawMetricDecay_rooted_of_factor_stronglyMeasurable
#print axioms YangMills.RG.norm_appendixFHoleKsharp_globalEval_le_ksharpRate_of_rawMetricDecay_rooted
#print axioms YangMills.RG.appendixFHoleKsharp_globalEval_eq_of_agreeOn
#print axioms YangMills.RG.appendixFHoleKsharp_globalEval_eq_of_agreeOn_skeleton
-- second Appendix-F hard-core gas from evaluated K#: structural only, with KP
-- exposed as a pointwise majorant hypothesis rather than as Dimock (642).
#print axioms YangMills.RG.appendixFHoleSecondGas_activity
#print axioms YangMills.RG.appendixFHoleSecondGasActivity_eq_zero_of_not_mem_targetRegion
#print axioms YangMills.RG.appendixFHoleSecondGasActivity_eq_of_agreeOn
#print axioms YangMills.RG.appendixFHoleSecondGasActivity_eq_of_agreeOn_skeleton
#print axioms YangMills.RG.appendixFHoleSecondGas_KPCriterion_of_majorant
-- spectator-integrated scalar K# normalization: structural bridge from the
-- finite K# target-family identity to the scalar zK family used by H#.
#print axioms YangMills.RG.appendixFHoleIntegratedKsharpActivity_eq_integral
#print axioms YangMills.RG.norm_appendixFHoleIntegratedKsharpActivity_le_of_globalEval_bound
#print axioms YangMills.RG.appendixFHoleIntegratedKsharpActivity_eq_zero_of_not_mem_targetRegion
#print axioms YangMills.RG.appendixFHoleIntegratedSecondGas_activity
#print axioms YangMills.RG.appendixFHoleIntegratedSecondGasKPMajorant_of_norm_bound
#print axioms YangMills.RG.integral_sum_appendixFHoleKsharp_eq_sum_prod_integratedKsharpActivity_of_admissibleTargetFamilies
-- second Ursell object H#: finite union-fiber bookkeeping only; no convergence
-- or residual estimate is hidden in the totalized `tsum` definition.
#print axioms YangMills.RG.appendixFHoleHsharpTerm_eq_sum_filter
#print axioms YangMills.RG.appendixFHoleHsharpTerm_eq_zero_of_no_union
#print axioms YangMills.RG.omegaHolePolymerSystem_ursell_eq
#print axioms YangMills.RG.appendixFHoleHsharpTerm_eq_of_activity_eq_on_union
#print axioms YangMills.RG.appendixFHoleHsharpTerm_eq_of_activity_eq_on_skeleton
#print axioms YangMills.RG.sum_appendixFHoleHsharpTerm_eq_clusterSum_term
#print axioms YangMills.RG.appendixFHoleHsharp_eq_of_activity_eq_on_union
#print axioms YangMills.RG.appendixFHoleHsharp_eq_of_activity_eq_on_skeleton
#print axioms YangMills.RG.appendixFHoleHsharpOfKsharp_eq
#print axioms YangMills.RG.appendixFHoleHsharpOfKsharp_eq_of_agreeOn
#print axioms YangMills.RG.appendixFHoleHsharpOfKsharp_eq_of_agreeOn_skeleton
#print axioms YangMills.RG.appendixFHoleHsharpOfIntegratedKsharp_eq
#print axioms YangMills.RG.appendixFHoleHsharpOfIntegratedKsharp_eq_of_agreeOn
#print axioms YangMills.RG.appendixFHoleHsharpOfIntegratedKsharp_eq_of_agreeOn_skeleton
-- residual H# adapter: source complex-norm estimates feed the real
-- omega-rooted UV-decay producer without hiding Dimock's analytic bound.
#print axioms YangMills.RG.complex_re_contracts_norm
#print axioms YangMills.RG.complex_im_contracts_norm
#print axioms YangMills.RG.clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharp_le
#print axioms YangMills.RG.rooted_clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharp_le
#print axioms YangMills.RG.summable_abs_of_omegaRootedAppendixFHsharp
#print axioms YangMills.RG.summable_abs_of_omegaRootedAppendixFHsharp_re
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
#print axioms YangMills.RG.summable_abs_of_omegaRootedAppendixFHsharpPartial
#print axioms YangMills.RG.summable_abs_of_omegaRootedAppendixFHsharpPartial_re
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
#print axioms YangMills.RG.summable_abs_of_omegaRootedAppendixFHsharp_of_partial_bounds
#print axioms YangMills.RG.summable_abs_of_omegaRootedAppendixFHsharp_re_of_partial_bounds
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
-- triple-infinity closure: order, rooted target, and scale budgets.
#print axioms YangMills.RG.orderTargetInfluence_le_of_geometric_leaf
#print axioms YangMills.RG.scaleInfluence_le_of_scale_budget
#print axioms YangMills.RG.tripleInfluence_le_of_geometric_leaf_scale_budget
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
#print axioms YangMills.RG.summable_abs_of_omegaRootedAppendixFHsharp_four_mul_margin_of_source_majorant
#print axioms YangMills.RG.summable_abs_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_source_majorant
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_source_majorant
#print axioms YangMills.RG.summable_abs_of_omegaRootedAppendixFHsharpOfIntegratedKsharp_re_four_mul_margin_of_source_majorant
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharpOfIntegratedKsharp_re_four_mul_margin_of_source_majorant
#print axioms YangMills.RG.lattice_mass_gap_marginal_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_source_majorant
#print axioms YangMills.RG.lattice_mass_gap_marginal_of_omegaRootedAppendixFHsharpOfIntegratedKsharp_re_four_mul_margin_of_source_majorant
#print axioms YangMills.RG.summable_abs_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_source_majorant
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
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootVertexSum
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootChildOrderSum
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootSum_eq_inv_factorial_mul_rawSum
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootChildOrderSum_eq_childFactorSum
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum_le_inv_succ_mul_rawSum
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootChildOrderSum_le_inv_succ_mul_rawSum
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum_le_four_pow_inv_succ_mul_vertexSum
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootChildOrderSum_le_four_pow_inv_succ_mul_vertexSum
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootSum_le_childFactorSum
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedIndexSum_eq_card_mul_root
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeTerm_le_markedSkeletonSum_of_mem_skeleton
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeTerm_le_markedSkeletonTreeTerm_of_mem_skeleton
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeTerm_le_markedIndexSum_of_mem_skeleton
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeTerm_le_card_mul_markedRootSum_of_mem_skeleton
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeTerm_le_card_mul_markedRootSum
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeTerm_le_four_pow_markedRootVertexSum
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeTerm_le_geometric_of_markedRootVertexSum
-- finite second-Ursell geometry for the future weighted leaf summation:
-- target metric stitching, rooted hard-core sums, and factorial moments.
#print axioms YangMills.RG.omegaClusterUnion_component_subset
#print axioms YangMills.RG.omegaClusterUnion_component_subset_of_eq
#print axioms YangMills.RG.omegaClusterUnion_component_skeleton_subset
#print axioms YangMills.RG.omegaClusterUnion_component_skeleton_subset_of_eq
#print axioms YangMills.RG.omegaClusterUnion_discreteModifiedMetric_add_one_le_sum_of_spanningTree
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeTerm_le_targetExpWeight_mul
#print axioms YangMills.RG.appendixFHole_incomp_expWeightSum_le_skeletonCard_mul
#print axioms YangMills.RG.appendixFSecondUrsellMomentConstant_one_le
#print axioms YangMills.RG.appendixFSecondUrsellMomentConstant_inv_le
#print axioms YangMills.RG.appendixFSecondUrsellMomentConstant_root_le
#print axioms YangMills.RG.appendixFSecondUrsellMomentConstant_nonneg
#print axioms YangMills.RG.appendixFHole_rootedFiniteMetricMomentExpWeightSum_le
#print axioms YangMills.RG.appendixFHole_containedMetricMomentExpWeightSum_le_metric_mul
#print axioms YangMills.RG.appendixFHole_incomp_expWeight_metricMomentSum_le_factorial_mul
#print axioms YangMills.RG.appendixFHoleIncompMomentKernel_nonneg
#print axioms YangMills.RG.appendixFHoleIncompMomentKernel_sum_le_factorial_mul
#print axioms YangMills.RG.appendixFHoleIncompMomentKernel_childMoment_mul
#print axioms YangMills.RG.appendixFHoleIncompMomentKernel_childMoment_sum_le_factorial_mul
#print axioms YangMills.RG.appendixFHoleIncompMomentKernel_normalizedChildMoment_sum_le_factorial_mul
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootRawSum_le_completeTreeParentSum
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootCompleteParentKernelSum_eq_sum_fixed
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootFixedParentKernelSum_eq_normalizedKernelSum
#print axioms YangMills.RG.appendixFHole_markedRootMetricMomentSum_le_factorial_mul
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootFixedTreeNormalizedKernelSum_le_of_vertexwise_walk_budget
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootFixedParentKernelSum_le_of_vertexwise_walk_budget
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootCompleteParentSum_le_kernelSum
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootFixedTreeNormalizedKernelSum_le_momentBudget
#print axioms YangMills.RG.appendixFSecondUrsellLeafConstant
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootFixedParentKernelSum_le_prod_childMomentBudget_mul_rootMoment
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootFixedParentKernelSum_le_childFactor_mul_momentPow
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootSum_le_geometric_of_expWeight
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeTerm_le_geometric_of_markedRootLeafSummation
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeTerm_le_geometric_of_expWeight_leafSummation
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeTerm_le_geometric_of_markedRootLeafSummation_of_skeleton_nonempty
-- source-facing cluster3 hole geometry: Ω as the active complement of holes
-- and the rooted local incompatibility contract consumed by Route A.
#print axioms YangMills.RG.skeleton_eq_inter_omegaRegion
#print axioms YangMills.RG.appendixFHole_incompatibleExpWeightSum_le_metric_mul_of_rooted
-- closed source-facing Dimock-II `cluster3` contract for H#.
#print axioms YangMills.RG.AppendixFHsharpCluster3Contract.of_unshifted_residual_bound
#print axioms YangMills.RG.AppendixFHsharpCluster3Contract.residual_bound
#print axioms YangMills.RG.norm_appendixFHoleHsharp_le_residual_of_cluster3_contract
#print axioms YangMills.RG.summable_abs_of_omegaRootedAppendixFHsharp_four_mul_margin_of_cluster3_contract
#print axioms YangMills.RG.summable_abs_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_cluster3_contract
#print axioms YangMills.RG.norm_appendixFHoleHsharpOfIntegratedKsharp_le_residual_of_cluster3_contract
#print axioms YangMills.RG.summable_abs_of_omegaRootedAppendixFHsharpOfIntegratedKsharp_re_four_mul_margin_of_cluster3_contract
#print axioms YangMills.RG.summable_abs_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_cluster3_contract
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_cluster3_contract
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharpOfIntegratedKsharp_re_four_mul_margin_of_cluster3_contract
-- CMP116 evaluated H# adapter: normal form plus full-target/skeleton support
-- dependencies inherited from the existing Appendix-F support package.
#print axioms YangMills.RG.balabanCMP116AppendixFHsharpOfKsharp_eq_hsharp
#print axioms YangMills.RG.balabanCMP116AppendixFHsharpOfKsharp_eq_of_agreeOn
#print axioms YangMills.RG.balabanCMP116AppendixFHsharpOfKsharp_eq_of_agreeOn_skeleton
-- source-facing packaged geometric H# profiles: one record now supplies the
-- summability, tail, residual, and UV consumers without duplicating fields.
#print axioms YangMills.RG.AppendixFHsharpGeometricMajorantProfile.summable_terms
#print axioms YangMills.RG.AppendixFHsharpGeometricMajorantProfile.tail_bound
#print axioms YangMills.RG.AppendixFHsharpGeometricMajorantProfile.residual_bound
#print axioms YangMills.RG.AppendixFHsharpGeometricMajorantProfile.summable_abs_of_profile
#print axioms YangMills.RG.AppendixFHsharpGeometricMajorantProfile.summable_abs_re_of_profile
#print axioms YangMills.RG.AppendixFHsharpGeometricMajorantProfile.singleScaleUVDecay_of_profile
#print axioms YangMills.RG.balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_weighted_tree_geometric
#print axioms YangMills.RG.balabanCMP116AppendixFHsharpCluster3Contract_of_weighted_tree_geometric
#print axioms YangMills.RG.summable_abs_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_profile
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_weighted_tree_geometric
-- marked-vertex source endpoint: the remaining leaf/root estimate may be
-- stated directly for the root-marked vertex-product sum.
#print axioms YangMills.RG.omegaPolymerReindex
#print axioms YangMills.RG.omegaPolymerReindex_val
#print axioms YangMills.RG.omegaPolymerSkeletonRoot
#print axioms YangMills.RG.omegaPolymerSkeletonRoot_mem
#print axioms YangMills.RG.finiteMarkedZeroProductSum_eq_rootSum_mul_leafSum_pow
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootVertexSum_eq_rooted_mul_total_pow
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeMarkedRootVertexSum_le_rootBudget_mul_leafBudget_pow
#print axioms YangMills.RG.appendixFHoleHsharpWeightedTreeTerm_le_geometric_of_canonicalMarkedRootVertexSum
#print axioms YangMills.RG.balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_markedRootVertex_geometric
#print axioms YangMills.RG.balabanCMP116AppendixFHsharpCluster3Contract_of_markedRootVertex_geometric
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_markedRootVertex_geometric
-- leaf-summation source endpoint: the finite marked-root leaf theorem now
-- feeds CMP116 profile/cluster3/UV consumers under explicit weight splits.
#print axioms YangMills.RG.appendixFSecondUrsellLeafConstant_nonneg
#print axioms YangMills.RG.appendixFSecondUrsellLeafConstant_one_le
#print axioms YangMills.RG.appendixFSecondUrsellMomentConstant_le_leafConstant
#print axioms YangMills.RG.appendixFHoleRootSumConstant_nonneg_of_hCq
#print axioms YangMills.RG.one_sub_inv_le_two_of_nonneg_of_le_half
#print axioms YangMills.RG.appendixFSecondUrsell_closed_le_four_mul_rawRoot
#print axioms YangMills.RG.appendixFSecondUrsell_sourceObligations_of_halfBudget
#print axioms YangMills.RG.balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_expWeight_leafSummation
#print axioms YangMills.RG.balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_pointwise_expWeight_leafSummation
#print axioms YangMills.RG.balabanCMP116AppendixFHsharpCluster3Contract_of_expWeight_leafSummation
#print axioms YangMills.RG.balabanCMP116AppendixFHsharpCluster3Contract_of_pointwise_expWeight_leafSummation
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_expWeight_leafSummation
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_pointwise_expWeight_leafSummation
#print axioms YangMills.RG.balabanCMP116AppendixFConnectedLocalActivity_globalEval_stronglyMeasurable
#print axioms YangMills.RG.BalabanCMP116LocalizedActivityFamily.activity_globalEval_stronglyMeasurable
#print axioms YangMills.RG.BalabanCMP116LocalizedActivityFamily.fluctuationSupport_subset_omega
#print axioms YangMills.RG.BalabanCMP116LocalizedActivityFamily.fluctuationSupport_subset_activeSupport
#print axioms YangMills.RG.BalabanCMP116LocalizedActivityFamily.activity_globalEval_eq_of_agreeOn_activeSupport
#print axioms YangMills.RG.BalabanCMP116LocalizedActivityFamily.mayerCoverActivity_fluctuationSupport_subset_omega
#print axioms YangMills.RG.BalabanCMP116LocalizedActivityFamily.mayerCoverActivity_fluctuationSupport_subset_activeUnion
#print axioms YangMills.RG.BalabanCMP116LocalizedActivityFamily.mayerCoverActivity_globalEval_eq_of_agreeOn_activeUnion_only
#print axioms YangMills.RG.BalabanCMP116AppendixFSupportHypotheses.activeSupport_subset_full
#print axioms YangMills.RG.BalabanCMP116AppendixFSupportHypotheses.of_activeSupport_subset_skeleton
#print axioms YangMills.RG.BalabanCMP116AppendixFSupportHypotheses.of_activeSupport_eq_skeleton
#print axioms YangMills.RG.physicalGaugeCMP116SupportHypotheses_of_transport
#print axioms YangMills.RG.balabanCMP116_hraw_of_physicalGaugeCMP116ActivityTransport
#print axioms YangMills.RG.BalabanCMP116AppendixFSupportHypotheses.of_activeSupport_subset_target_inter_omegaRegion
#print axioms YangMills.RG.BalabanCMP116AppendixFSupportHypotheses.of_activeSupport_eq_target_inter_omegaRegion
#print axioms YangMills.RG.BalabanCMP116AppendixFSupportHypotheses.zeta_eq_zero_imp_not_disjoint_skeleton_of_activeSupport_subset_target_inter_omegaRegion
#print axioms YangMills.RG.BalabanCMP116AppendixFSupportHypotheses.omegaGraph_adj_imp_skeletonOverlapGraph_adj_of_activeSupport_subset_target_inter_omegaRegion
#print axioms YangMills.RG.BalabanCMP116AppendixFSupportHypotheses.zeta_eq_zero_iff_not_disjoint_skeleton_of_activeSupport_eq_target_inter_omegaRegion
#print axioms YangMills.RG.BalabanCMP116AppendixFSupportHypotheses.omegaGraph_adj_iff_skeletonOverlapGraph_adj_of_activeSupport_eq_target_inter_omegaRegion
#print axioms YangMills.RG.balabanCMP116AppendixFConnectedLocalActivity_globalEval_eq_of_agreeOn
#print axioms YangMills.RG.balabanCMP116AppendixFConnectedLocalActivity_globalEval_eq_of_agreeOn_skeleton
#print axioms YangMills.RG.balabanCMP116AppendixFKsharp_globalEval_eq_of_agreeOn
#print axioms YangMills.RG.balabanCMP116AppendixFKsharp_globalEval_eq_of_agreeOn_skeleton
#print axioms YangMills.RG.balabanCMP116AppendixFSecondGasActivity_eq_of_agreeOn
#print axioms YangMills.RG.balabanCMP116AppendixFSecondGasActivity_eq_of_agreeOn_skeleton
#print axioms YangMills.RG.balabanCMP116AppendixFConnectedLocalActivity_globalEval_stronglyMeasurable_of_source
#print axioms YangMills.RG.norm_balabanCMP116AppendixFKsharp_globalEval_le_ksharpRate_of_rawMetricDecay_rooted
#print axioms YangMills.RG.integrable_balabanCMP116AppendixFConnectedLocalActivity_of_rawMetricDecay_rooted
#print axioms YangMills.RG.integrable_balabanCMP116AppendixFConnectedLocalActivity_of_rawMetricDecay_rooted_of_stronglyMeasurable
#print axioms YangMills.RG.integrable_balabanCMP116AppendixFConnectedLocalActivity_of_rawMetricDecay_rooted_of_factor_stronglyMeasurable
#print axioms YangMills.RG.integrable_balabanCMP116AppendixFConnectedLocalActivity_of_rawMetricDecay_rooted_of_source
#print axioms YangMills.RG.norm_balabanCMP116AppendixFIntegratedKsharpActivity_le_ksharpRate_of_rawMetricDecay_rooted
#print axioms YangMills.RG.norm_balabanCMP116AppendixFIntegratedKsharpActivity_le_ksharpRate_of_rawMetricDecay_rooted_of_source
#print axioms YangMills.RG.norm_balabanCMP116AppendixFIntegratedKsharpActivity_le_ksharpRate_of_transport
#print axioms YangMills.RG.BalabanCMP116AppendixFIntegratedSecondGasKPMajorant_of_rawMetricDecay_rooted_of_source
#print axioms YangMills.RG.BalabanCMP116AppendixFIntegratedSecondGasKPMajorant_of_rawMetricDecay_rooted_of_source_of_card_le_metric
#print axioms YangMills.RG.balabanCMP116AppendixFIntegratedSecondGas_KPCriterion_of_rawMetricDecay_rooted_of_source_of_card_le_metric
#print axioms YangMills.RG.balabanCMP116AppendixFIntegratedKsharpActivityFamily_norm_le_ksharpRate_of_rawMetricDecay_rooted
#print axioms YangMills.RG.balabanCMP116AppendixFIntegratedKsharpActivityFamily_norm_le_ksharpRate_of_rawMetricDecay_rooted_of_source
#print axioms YangMills.RG.balabanCMP116AppendixFIntegratedKsharpActivityFamily_norm_le_residual_mul_leaf_of_ksharpRate
#print axioms YangMills.RG.balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_pointwise_ksharpRate_leafSummation
#print axioms YangMills.RG.balabanCMP116AppendixFConnectedLocalActivity_hint_of_rawMetricDecay_rooted
#print axioms YangMills.RG.balabanCMP116AppendixFConnectedLocalActivity_hint_of_rawMetricDecay_rooted_of_stronglyMeasurable
#print axioms YangMills.RG.balabanCMP116AppendixFHsharpCluster3Contract_of_pointwise_ksharpRate_leafSummation
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_pointwise_ksharpRate_leafSummation
#print axioms YangMills.RG.balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_rawMetricDecay_rooted_ksharpRate
#print axioms YangMills.RG.balabanCMP116AppendixFHsharpCluster3Contract_of_rawMetricDecay_rooted_ksharpRate
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_rawMetricDecay_rooted_ksharpRate
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_rawMetricDecay_rooted_leafSummation
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_rawMetricDecay_rooted_leafSummation_of_halfBudget
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_rawMetricDecay_rooted_canonicalRoot_halfBudget
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_rawMetricDecay_rooted_canonicalRoot_halfBudget_of_aestronglyMeasurable
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_rawMetricDecay_rooted_canonicalRoot_halfBudget_of_stronglyMeasurable
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_rawMetricDecay_rooted_canonicalRoot_halfBudget_of_factor_stronglyMeasurable
#print axioms YangMills.RG.singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_rawMetricDecay_rooted_canonicalRoot_halfBudget_of_sourceMeasurable

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

#print axioms YangMills.RG.BalabanCMP116RawMetricDecay
#print axioms YangMills.RG.BalabanCMP116LocalizedActivityFamily.of_physicalLocalizedGaussianActivityCertificate
#print axioms YangMills.RG.balabanCMP116RawMetricDecay_of_physicalGaugeRawActivityDecay
#print axioms YangMills.RG.CMP116FluctuationField
#print axioms YangMills.RG.cmp116FieldProjection
#print axioms YangMills.RG.cmp116FieldProjection_comp
#print axioms YangMills.RG.OperatorSupportedBetween
#print axioms YangMills.RG.OperatorSupportedBetween.eq_of_agreeOn
#print axioms YangMills.RG.OperatorSupportedBetween.apply_eq_zero_outside
#print axioms YangMills.RG.OperatorSupportedBetween.add
#print axioms YangMills.RG.OperatorSupportedBetween.finsetSum
#print axioms YangMills.RG.OperatorSupportedBetween.comp
#print axioms YangMills.RG.OperatorSupportedBetween.mono
#print axioms YangMills.RG.singleCMP116CubeField
#print axioms YangMills.RG.cmp116Field_eq_sum_singleCube
#print axioms YangMills.RG.map_cmp116Field_eq_sum_singleCube
#print axioms YangMills.RG.CMP116LinearMapKernelBound
#print axioms YangMills.RG.CMP116KernelFiniteRange
#print axioms YangMills.RG.cmp116FiniteRangeClosure
#print axioms YangMills.RG.OperatorSupportedBetween.of_singleBond_kernel_zero
#print axioms YangMills.RG.OperatorSupportedBetween.of_kernel_bound_finiteRange
#print axioms YangMills.RG.CMP116LocalizedLinearMap
#print axioms YangMills.RG.CMP116LocalizedLinearMap.eq_of_agreeOn
#print axioms YangMills.RG.CMP116LocalizedLinearMap.apply_eq_zero_outside
#print axioms YangMills.RG.CMP116LocalizedLinearMap.add_toContinuousLinearMap
#print axioms YangMills.RG.CMP116LocalizedLinearMap.add_eq_of_agreeOn
#print axioms YangMills.RG.CMP116LocalizedLinearMap.add_apply_eq_zero_outside
#print axioms YangMills.RG.CMP116LocalizedLinearMap.finsetSum_toContinuousLinearMap
#print axioms YangMills.RG.CMP116LocalizedLinearMap.finsetSum_eq_of_agreeOn
#print axioms YangMills.RG.CMP116LocalizedLinearMap.finsetSum_apply_eq_zero_outside
#print axioms YangMills.RG.CMP116LocalizedLinearMap.finsetSumVarying
#print axioms YangMills.RG.CMP116LocalizedLinearMap.finsetSumVarying_toContinuousLinearMap
#print axioms YangMills.RG.CMP116LocalizedLinearMap.finsetSumVarying_eq_of_agreeOn
#print axioms YangMills.RG.CMP116LocalizedLinearMap.finsetSumVarying_apply_eq_zero_outside
#print axioms YangMills.RG.CMP116LocalizedLinearMap.comp_toContinuousLinearMap
#print axioms YangMills.RG.CMP116LocalizedLinearMap.comp_eq_of_agreeOn
#print axioms YangMills.RG.CMP116LocalizedLinearMap.comp_apply_eq_zero_outside
#print axioms YangMills.RG.CMP116LocalizedLinearMap.ofProjection
#print axioms YangMills.RG.CMP116LocalizedLinearMap.ofProjection_toContinuousLinearMap
#print axioms YangMills.RG.CMP116LocalizedLinearMap.ofProjection_eq_of_agreeOn
#print axioms YangMills.RG.CMP116LocalizedLinearMap.ofProjection_apply_eq_zero_outside
#print axioms YangMills.RG.physicalBondProjection
#print axioms YangMills.RG.physicalBondsOver
#print axioms YangMills.RG.cmp116OperatorOfPhysical
#print axioms YangMills.RG.PhysicalRootToCMP116OperatorTransport
#print axioms YangMills.RG.PhysicalRootToCMP116OperatorTransport.rootOperator
#print axioms YangMills.RG.PhysicalRootToCMP116OperatorTransport.localizedRootOperator
#print axioms YangMills.RG.PhysicalRootToCMP116OperatorTransport.rootOperator_kernelBound_of_certificate
#print axioms YangMills.RG.PhysicalRootToCMP116OperatorTransport.localizedRootOperator_supportedBetween
#print axioms YangMills.RG.PhysicalRootToCMP116OperatorTransport.localizedRootOperator_eq_of_agreeOn
#print axioms YangMills.RG.PhysicalRootToCMP116OperatorTransport.localizedRootOperator_apply_eq_zero_outside
#print axioms YangMills.RG.PhysicalRootToCMP116OperatorTransport.localizedRootLinearMap
#print axioms YangMills.RG.CMP116CoordIndex
#print axioms YangMills.RG.PhysicalGaugeCoordIndex
#print axioms YangMills.RG.PhysicalGaugeCMP116SiteMap
#print axioms YangMills.RG.PhysicalGaugeCMP116SiteMap.physicalBondsOver
#print axioms YangMills.RG.PhysicalGaugeCMP116SiteMap.physicalBondsOver_union
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.physicalBondsOfCells
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.image_bondToCube_subset_iff_physicalBondsOfCells
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.coordEquiv_symm_cell
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.sunLieCoordOfScalars
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.sunLieCoordScalar
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.pullFluctuationCochain
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.pullFluctuationAtBond
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.pullFluctuationCochain_apply
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.pushFluctuation
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.pushFluctuation_pullFluctuationCochain
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.pullFluctuationCochain_pushFluctuation
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.fluctuationFieldLinearEquiv
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.pullFluctuationCochain_agreeOn_iff
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.PhysicalGaugeCMP116GaussianChange
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.fluctuationFieldContinuousLinearEquiv
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.norm_pullFluctuationCochain_le
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.norm_pushFluctuation_le
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.norm_le_inverse_opNorm_mul_norm_pullFluctuationCochain
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.norm_le_opNorm_mul_norm_pushFluctuation
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.fluctuationFieldContinuousLinearEquiv_support_projection
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.gaussianRootMap
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.norm_gaussianRootMap_le
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.norm_gaussianRootMap_apply_le
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.norm_gaussianRootMap_le_of_root_norm_le
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.norm_gaussianRootMap_apply_le_of_root_norm_le
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.norm_gaussianRootMap_le_of_covarianceRootCertificate
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.norm_gaussianRootMap_apply_le_of_covarianceRootCertificate
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.gaussianRootMap_eq_coordinates_comp_cmp116OperatorOfPhysical
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.PhysicalGaugeCMP116GaussianChange.ofDictionaryRoot
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.PhysicalGaugeCMP116GaussianChange.integral_gaussianCoordinateMap_eq
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.PhysicalGaugeCMP116GaussianChange.integral_ofDictionaryRoot
#print axioms YangMills.RG.PhysicalRootToCMP116OperatorTransport.ofDictionary
#print axioms YangMills.RG.PhysicalRootToCMP116OperatorTransport.localizedRootLinearMap_ofDictionary
#print axioms YangMills.RG.PhysicalRootToCMP116OperatorTransport.localizedRootLinearMap_ofDictionary_toContinuousLinearMap
#print axioms YangMills.RG.PhysicalRootToCMP116OperatorTransport.localizedRootLinearMapFinsetSum_ofDictionary
#print axioms YangMills.RG.PhysicalRootToCMP116OperatorTransport.localizedRootLinearMapFinsetSum_ofDictionary_toContinuousLinearMap
#print axioms YangMills.RG.PhysicalRootToCMP116OperatorTransport.localizedRootLinearMapFinsetSum_ofDictionary_eq_of_agreeOn
#print axioms YangMills.RG.PhysicalRootToCMP116OperatorTransport.localizedRootLinearMapFinsetSum_ofDictionary_apply_eq_zero_outside
#print axioms YangMills.RG.PhysicalRootToCMP116OperatorTransport.localizedRootLinearMapFinsetSum_ofDictionary_pull_eq_of_agreeOn
#print axioms YangMills.RG.PhysicalRootToCMP116OperatorTransport.localizedRootLinearMapFinsetSum_ofDictionary_pull_apply_eq_zero_outside
#print axioms YangMills.RG.PhysicalRootToCMP116OperatorTransport.localizedRootLinearMapFinsetSum_ofDictionary_activity_globalEval_eq_of_agreeOn
#print axioms YangMills.RG.PhysicalRootToCMP116OperatorTransport.ActivityLocalRootPieceAgreement
#print axioms YangMills.RG.PhysicalRootToCMP116OperatorTransport.activityLocalRootPieceAgreement_of_agreeOn_activeSupport
#print axioms YangMills.RG.PhysicalRootToCMP116OperatorTransport.gaussianRootMap_agreeOn_activity_fluctuationSupport_of_cmp116_agreeOn
#print axioms YangMills.RG.PhysicalRootToCMP116OperatorTransport.gaussianRootMap_activity_globalEval_eq_of_agreeOn_of_localizedRootLinearMapFinsetSum
#print axioms YangMills.RG.PhysicalRootToCMP116OperatorTransport.localizedRootLinearMapFinsetSum_ofDictionary_activityFamily_sum_globalEval_eq_of_agreeOn
#print axioms YangMills.RG.PhysicalRootToCMP116OperatorTransport.localizedRootLinearMapFinsetSum_ofDictionary_activityFamily_finsetSum_globalEval_eq_of_agreeOn
#print axioms YangMills.RG.PhysicalRootToCMP116OperatorTransport.localizedRootLinearMapFinsetSum_ofDictionary_mayerCoverActivity_globalEval_eq_of_agreeOn
#print axioms YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses
#print axioms YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses.gaussianChange
#print axioms YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses.integral_gaussianRootMap_eq
#print axioms YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses.integral_physicalActivity_gaussianRootMap_eq
#print axioms YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
#print axioms YangMills.RG.physicalGaugeRawActivityDecay_of_cmp116RawSource
#print axioms YangMills.RG.physicalLocalizedGaussianActivityCertificate_of_cmp116Source
#print axioms YangMills.RG.physicalLocalizedGaussianActivityCertificate_of_cmp116RawSource
#print axioms YangMills.RG.PhysicalGaugeCMP116ActivityTransport.of_cmp116RawSource
#print axioms YangMills.RG.physicalGaugeCMP116ActivityTransport_of_cmp116RawSource
#print axioms YangMills.RG.physicalGaugeCMP116SupportHypotheses_of_cmp116RawSource
#print axioms YangMills.RG.balabanCMP116RawMetricDecay_of_cmp116RawSource
#print axioms YangMills.RG.balabanCMP116_hraw_of_cmp116RawSource
#print axioms YangMills.RG.physicalGaugeCMP116RawSourceScaleFamily
#print axioms YangMills.RG.singleScaleUVDecay_of_cmp116RawSource_hsharp
#print axioms YangMills.RG.lattice_mass_gap_of_singleScaleUVDecay_marginal
#print axioms YangMills.RG.cmp116RawHsharpUVAmplitude
#print axioms YangMills.RG.lattice_mass_gap_of_cmp116RawSource_hsharp_marginal
#print axioms YangMills.RG.lattice_mass_gap_of_cmp116RawSourceM3Frontier
#print axioms YangMills.RG.singlePhysicalBondCochain_eq_toLp_single
#print axioms YangMills.RG.norm_singlePhysicalBondCochain
#print axioms YangMills.RG.physicalCovarianceKernelBound_const_opNorm
#print axioms YangMills.RG.M3FrontierDependencyGraph.isAcyclic_eq_true
#print axioms YangMills.RG.M3FrontierDependencyGraph.allFrontierFieldsCovered_eq_true
#print axioms YangMills.RG.M3FrontierDependencyGraph.allFrontierFieldsUsed_eq_true
#print axioms YangMills.RG.M3FrontierDependencyGraph.derivedNodesHavePositiveRank_eq_true
#print axioms YangMills.RG.M3FrontierDependencyGraph.nonterminalDerivedNodesUsed_eq_true
#print axioms YangMills.RG.M3FrontierDependencyGraph.marginalAssemblyDependsOnAllFrontierFields_eq_true
#check YangMills.RG.BalabanCMP116SourceAssumptions
#check YangMills.RG.BalabanCMP116SourceAssumptions.rawSource
#print axioms YangMills.RG.BalabanCMP116SourceAssumptions.rooted_hsharp_remainder_identity_rawSource
#check YangMills.RG.BalabanCMP116SourceTheorem
#print axioms YangMills.RG.cmp116Lemma3Weight
#print axioms YangMills.RG.cmp116Lemma3Weight_nonneg
#print axioms YangMills.RG.balabanCMP116Lemma3DecayRate
#print axioms YangMills.RG.balabanCMP116Lemma3Weight
#print axioms YangMills.RG.CMP116Lemma3ActivityEstimate
#print axioms YangMills.RG.balabanLemma3_rawActivityDecay
#print axioms YangMills.RG.balabanCMP116Lemma3Weight_nonneg
#print axioms YangMills.RG.balabanCMP116Lemma3Weight_domination
#print axioms YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.of_lemma3ActivityEstimate
#print axioms YangMills.RG.CMP116Lemma3Parameters
#print axioms YangMills.RG.CMP116HResummation
#print axioms YangMills.RG.cmp116HIndexFinset
#print axioms YangMills.RG.balabanCMP116H
#print axioms YangMills.RG.norm_balabanCMP116H_le_termWeightSum
#print axioms YangMills.RG.cmp116Lemma3ActivityEstimate_of_resummation
#print axioms YangMills.RG.cmp116Lemma3ScaleWeight
#print axioms YangMills.RG.cmp116Lemma3ScaleAmplitude
#print axioms YangMills.RG.cmp116Lemma3ScaleWeight_nonneg
#print axioms YangMills.RG.CMP116Lemma3ActivityEstimateScaleFamily
#print axioms YangMills.RG.CMP116Lemma3ActivityTermwiseScaleBoundary
#print axioms YangMills.RG.rawSource_of_lemma3ActivityEstimate
#print axioms YangMills.RG.rawSource_of_lemma3ActivityEstimate_gaussianNormalization
#print axioms YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.of_lemma3ActivityEstimateScaleFamily
#print axioms YangMills.RG.rawSource_of_weightedPostPBoundaries
#print axioms YangMills.RG.rawSource_of_weightedPostPBoundaries_gaussianNormalization
#print axioms YangMills.RG.rawSource_of_eq231_weightedPostPBoundaries
#print axioms YangMills.RG.rawSource_of_eq231_weightedPostPBoundaries_gaussianNormalization
#print axioms YangMills.RG.rawSource_of_eq231_sourcePIndexMemIff_gaussianNormalization
#print axioms YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq231_boundaries
#print axioms YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.rawSource
#print axioms YangMills.RG.cmp116Lemma3ActivityEstimateScaleFamily_of_resummation
#print axioms YangMills.RG.cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_postD
#print axioms YangMills.RG.cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_residualStages
#print axioms YangMills.RG.cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStageResidualStages
#print axioms YangMills.RG.cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStagePostPResidualBound
#print axioms YangMills.RG.CMP116Lemma3PostPScaleSourceAssumptions
#print axioms YangMills.RG.CMP116Lemma3PostPScaleSourceAssumptions.activityTermwiseBoundary
#print axioms YangMills.RG.CMP116Lemma3PostPScaleSourceAssumptions.lemma3_activity_estimate
#print axioms YangMills.RG.cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStageSourceBound_residualStages
#print axioms YangMills.RG.cmp116AdmissibleMetricZeroExtension
#print axioms YangMills.RG.cmp116Lemma3ActivityEstimate_of_admissible_zeroExtension
#print axioms YangMills.RG.CMP116Lemma3AdmissibleActivityEstimateScaleFamily
#print axioms YangMills.RG.cmp116AdmissibleMetricScaleExtension
#print axioms YangMills.RG.cmp116Lemma3ActivityEstimateScaleFamily_of_admissible_zeroExtension
#print axioms YangMills.RG.CMP116Lemma3PostPScaleSourceAssumptions.lemma3_activity_estimate_admissible_zeroExtension
#print axioms YangMills.RG.balabanCMP116Lemma3Weight_domination_of_admissible_metricComparison
#print axioms YangMills.RG.cmp116Eq229Weight
#print axioms YangMills.RG.cmp116Eq229Product
#print axioms YangMills.RG.CMP116Eq229Summability
#print axioms YangMills.RG.cmp116Eq229Weight_nonneg
#print axioms YangMills.RG.cmp116Eq229Product_nonneg
#print axioms YangMills.RG.cmp116_DStage_sum_le_of_eq229
#print axioms YangMills.RG.CMP116PStageSummability
#print axioms YangMills.RG.cmp116H_postDSum_le_of_pStage
#print axioms YangMills.RG.cmp116H_termWeightSum_eq_nested
#print axioms YangMills.RG.cmp116H_termWeightSum_le_of_eq229
#print axioms YangMills.RG.cmp116Lemma3ActivityEstimate_of_eq229_postD
#print axioms YangMills.RG.CMP116Eq231PBondBoundary
#print axioms YangMills.RG.CMP116Eq231EligibleBondCarrierSource
#print axioms YangMills.RG.CMP116Eq231PositiveTailOwnershipSource
#print axioms YangMills.RG.CMP116Eq231InteriorBoundaryAdmissibilitySource
#print axioms YangMills.RG.CMP116Eq231FullCarrierAdmissibilitySource
#print axioms YangMills.RG.CMP116Eq231Y0cStarInteriorBoundaryToGapSource
#print axioms YangMills.RG.cmp116Eq231_y0cStarInteriorBoundary_to_gapCubes_of_source
#print axioms YangMills.RG.CMP116Eq231PositiveTailOwnershipSource.of_y0cStarInteriorBoundary
#print axioms YangMills.RG.exists_fullCarrierAdmissibility_without_y0cStarInteriorBoundaryToGapSource
#print axioms YangMills.RG.CMP116Eq231PositiveTailOwnershipSource.of_interiorBoundary
#print axioms YangMills.RG.cmp116Eq231_bond_fst_mem_gapCubes_of_interiorBoundary
#print axioms YangMills.RG.cmp116Eq231_bond_fst_mem_gapCubes_of_y0cStarInteriorBoundary
#print axioms YangMills.RG.cmp116Eq231_bond_fst_mem_gapCubes_of_sourceEligible
#print axioms YangMills.RG.cmp116Eq231_bond_fst_mem_gapCubes_of_positiveTailOwnership
#print axioms YangMills.RG.CMP116Eq231EligibleBondCarrierSource.of_positiveTailOwnership
#print axioms YangMills.RG.cmp116Eq231SourcePIndex
#print axioms YangMills.RG.cmp116Eq231SourcePIndex_mem_iff
#print axioms YangMills.RG.cmp116Eq231PIndex_eq_sourceFilteredBondSets_of_mem_iff
#print axioms YangMills.RG.CMP116Eq231BalabanPFamilySourcePackage.of_sourceEligibleBondCarrier
#print axioms YangMills.RG.CMP116Eq231BalabanPFamilySourcePackage.of_positiveTailOwnership
#print axioms YangMills.RG.CMP116Eq231BalabanPFamilySourcePackage.of_interiorBoundary
#print axioms YangMills.RG.cmp116Eq231_sourcePIndexMemIff_of_positiveTailOwnership
#print axioms YangMills.RG.cmp116Eq231SourcePIndex_subset_carrier
#print axioms YangMills.RG.CMP116Eq231PBondBoundary.of_positiveTailOwnership
#print axioms YangMills.RG.cmp116Eq231PWeight
#print axioms YangMills.RG.cmp116Eq231_rate_condition_of_source_smallness
#print axioms YangMills.RG.cmp116Eq231_rate_condition_of_source_bracket
#print axioms YangMills.RG.cmp116PGeometricFamilySummation_of_eq231
#print axioms YangMills.RG.cmp116PStageSourceBound_of_eq231_pointwise
#print axioms YangMills.RG.CMP116PResidualSummability
#print axioms YangMills.RG.cmp116Eq229WeightedPWeight
#print axioms YangMills.RG.cmp116Eq229WeightedPWeight_nonneg
#print axioms YangMills.RG.cmp116PStageSummability_of_pResidualSummability_weighted
#print axioms YangMills.RG.cmp116PStageSummabilityScaleFamily_of_pResidualSummability_weighted
#print axioms YangMills.RG.cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_weightedPResidualPostPResidualBound
#print axioms YangMills.RG.CMP116PStageSourceBound
#print axioms YangMills.RG.cmp116PStageSourceBound_of_pointwise_geometric
#print axioms YangMills.RG.cmp116PResidualSummability_of_pStageSourceBound
#print axioms YangMills.RG.CMP116Z0ResidualSummability
#print axioms YangMills.RG.CMP116Z0StageSourceBound
#print axioms YangMills.RG.cmp116Z0ResidualSummability_of_z0StageSourceBound
#print axioms YangMills.RG.CMP116Z0PrimeResidualSummability
#print axioms YangMills.RG.CMP116PostPResidualSourceBound
#print axioms YangMills.RG.CMP116PostPResidualBound
#print axioms YangMills.RG.cmp116PostPResidualBound_of_sourceBound
#print axioms YangMills.RG.CMP116PostPResidualSourceMajorizationScaleFamily
#print axioms YangMills.RG.cmp116Eq237Z0PrimeIndex
#print axioms YangMills.RG.cmp116Eq237Z0Fiber
#print axioms YangMills.RG.cmp116Eq237_nested_sum_eq_fiber_sum
#print axioms YangMills.RG.cmp116Eq237Amplitude
#print axioms YangMills.RG.cmp116Eq237Amplitude_nonneg
#print axioms YangMills.RG.cmp116Eq237FixedZ0PrimeWeight
#print axioms YangMills.RG.cmp116Eq237FixedZ0PrimeWeight_nonneg
#print axioms YangMills.RG.cmp116PostPResidualSourceBound_of_eq237
#print axioms YangMills.RG.CMP116Eq237MajorizationBoundary
#print axioms YangMills.RG.cmp116Eq237_residualExponent_absorbed
#print axioms YangMills.RG.cmp116PostPResidualSourceMajorizationScaleFamily_of_eq237
#print axioms YangMills.RG.cmp116PostPResidualBoundScaleFamily_of_sourceBound
#print axioms YangMills.RG.CMP116Lemma3Eq229ScaleBoundary
#print axioms YangMills.RG.CMP116Lemma3PStageSourceScaleBoundary
#print axioms YangMills.RG.CMP116Lemma3PStageSourceScaleBoundary.of_pointwise_geometric
#print axioms YangMills.RG.CMP116Lemma3PStageSourceScaleBoundary.of_eq231_pointwise
#print axioms YangMills.RG.CMP116Lemma3PStageSourceScaleBoundary.of_eq231_sourceBondSets
#print axioms YangMills.RG.CMP116Lemma3PStageSourceScaleBoundary.of_eq231_filteredBondSets
#print axioms YangMills.RG.CMP116Lemma3PStageSourceScaleBoundary.p_residual_summability
#print axioms YangMills.RG.CMP116Lemma3WeightedPostPSourceScaleBoundary
#print axioms YangMills.RG.CMP116Lemma3WeightedPostPSourceScaleBoundary.of_sourceBound_eq237Majorization
#print axioms YangMills.RG.CMP116Lemma3WeightedPostPSourceScaleBoundary.of_eq237
#print axioms YangMills.RG.CMP116Lemma3WeightedPostPSourceScaleBoundary.postP_residual_bound
#print axioms YangMills.RG.cmp116H_postP_sum_le_of_residualStages
#print axioms YangMills.RG.cmp116PostPResidualBound_of_residualStages
#print axioms YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions
#print axioms YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.activityTermwiseBoundary
#print axioms YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_boundaries
#print axioms YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq237Majorization
#print axioms YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq237
#print axioms YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq231_filteredBondSets
#print axioms YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.p_residual_summability
#print axioms YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.postP_residual_bound
#print axioms YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate
#print axioms YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_boundaries
#print axioms YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq237Majorization
#print axioms YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq237
#print axioms YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq231_boundaries
#print axioms YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq231_filteredBondSets
#print axioms YangMills.RG.cmp116H_postD_sum_le_of_residualStages
#print axioms YangMills.RG.cmp116H_postD_sum_le_of_pStageSourceBound_residualStages
#print axioms YangMills.RG.cmp116H_termWeightSum_le_of_eq229_of_residualStages
#print axioms YangMills.RG.cmp116H_termWeightSum_le_of_eq229_of_pStageSourceBound_residualStages
#print axioms YangMills.RG.cmp116Lemma3ActivityEstimate_of_eq229_pStageSourceBound_residualStages
#print axioms YangMills.RG.cmp116H_postD_sum_le_of_pStageResidualStages
#print axioms YangMills.RG.cmp116H_termWeightSum_le_of_eq229_of_pStageResidualStages
#print axioms YangMills.RG.cmp116Lemma3ActivityEstimate_of_eq229_pStageResidualStages
#print axioms YangMills.RG.cmp116H_postD_sum_le_of_pStagePostPResidualBound
#print axioms YangMills.RG.cmp116H_termWeightSum_le_of_eq229_of_pStagePostPResidualBound
#print axioms YangMills.RG.cmp116Lemma3ActivityEstimate_of_eq229_pStagePostPResidualBound
#print axioms YangMills.RG.CMP116RawSourceM3Frontier.of_balabanSourceAssumptions
#print axioms YangMills.RG.BalabanCMP116SourceAssumptions.to_m3Frontier
#print axioms YangMills.RG.balabanCMP116SourceTheorem_of_assumptions
#print axioms YangMills.RG.BalabanCMP116Lemma3SourceAssumptions
#print axioms YangMills.RG.BalabanCMP116Lemma3SourceAssumptions.rawSource
#print axioms YangMills.RG.BalabanCMP116Lemma3SourceAssumptions.rooted_hsharp_remainder_identity_rawSource
#print axioms YangMills.RG.CMP116RawSourceM3Frontier.of_lemma3SourceAssumptions
#print axioms YangMills.RG.BalabanCMP116Lemma3SourceAssumptions.to_m3Frontier
#print axioms YangMills.RG.BalabanCMP116Lemma3WeightedPostPSourceAssumptions
#print axioms YangMills.RG.BalabanCMP116Lemma3WeightedPostPSourceAssumptions.lemma3_activity_estimate
#print axioms YangMills.RG.BalabanCMP116Lemma3WeightedPostPSourceAssumptions.rawSource
#print axioms YangMills.RG.BalabanCMP116Lemma3WeightedPostPSourceAssumptions.to_lemma3SourceAssumptions
#print axioms YangMills.RG.BalabanCMP116Lemma3WeightedPostPSourceAssumptions.of_eq231_boundaries
#print axioms YangMills.RG.CMP116RawSourceM3Frontier.of_lemma3WeightedPostPSourceAssumptions
#print axioms YangMills.RG.CMP116RawSourceM3Frontier.of_eq231WeightedPostPSourceBoundaries
#print axioms YangMills.RG.BalabanCMP116Lemma3WeightedPostPSourceAssumptions.to_m3Frontier
#print axioms YangMills.RG.BalabanCMP116Lemma3WeightedPostPSourceAssumptions.lattice_mass_gap_marginal
#print axioms YangMills.RG.CMP116RawSourceM3Frontier.of_lemma3ResummationSourceAssumptions
#print axioms YangMills.RG.BalabanCMP116Lemma3ResummationSourceAssumptions
#print axioms YangMills.RG.BalabanCMP116Lemma3ResummationSourceAssumptions.lemma3_activity_estimate
#print axioms YangMills.RG.BalabanCMP116Lemma3ResummationSourceAssumptions.rawSource
#print axioms YangMills.RG.BalabanCMP116Lemma3ResummationSourceAssumptions.to_lemma3SourceAssumptions
#print axioms YangMills.RG.BalabanCMP116Lemma3ResummationSourceAssumptions.to_m3Frontier
#print axioms YangMills.RG.BalabanCMP116Lemma3ResummationSourceAssumptions.lattice_mass_gap_marginal
#check YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.of_components
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.CMP116GaussianCoordinateMapSource
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.CMP116GaussianPhysicalLawSource
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.CMP116GaussianNormalizedPushforwardSource
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.CMP116GaussianPushforwardNormalization.of_sourceNormalizedChange
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.CMP116GaussianPushforwardNormalization.of_sourceRecords
#print axioms YangMills.RG.PhysicalGaugeCMP116Dictionary.CMP116GaussianPushforwardNormalization.gaussian_pushforward
#print axioms YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses.of_gaussianNormalization
#print axioms YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses.of_sourceRecords
#print axioms YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.of_gaussianNormalization
#print axioms YangMills.RG.PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.of_sourceRecords
#print axioms YangMills.RG.cmp116GaussianPushforwardNormalizationScaleFamily_of_sourceRecords
#print axioms YangMills.RG.rawSource_of_lemma3ActivityEstimate_sourceRecords
#print axioms YangMills.RG.rawSource_of_weightedPostPBoundaries_sourceRecords
#print axioms YangMills.RG.rawSource_of_eq231_weightedPostPBoundaries_sourceRecords
#print axioms YangMills.RG.rawSource_of_eq231_sourcePIndexMemIff_sourceRecords
#print axioms YangMills.RG.CMP116Lemma3PStageSourceScaleBoundary.of_eq231_positiveTailOwnership
#print axioms YangMills.RG.CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq231_positiveTailOwnership
#print axioms YangMills.RG.PhysicalGaugeCMP116RawHsharpFrontier
#print axioms YangMills.RG.PhysicalGaugeCMP116RawHsharpFrontier.singleScaleUVDecay
#print axioms YangMills.RG.PhysicalGaugeCMP116RawHsharpFrontier.lattice_mass_gap_marginal
#print axioms YangMills.RG.CMP116RawSourceM3Frontier.toRawHsharpFrontier
#print axioms YangMills.RG.CMP116RawSourceM3Frontier.singleScaleUVDecay
#print axioms YangMills.RG.CMP116RawSourceM3Frontier.lattice_mass_gap_marginal
#print axioms YangMills.RG.BalabanCMP116LocalizedActivityFamily.ofDictionary
#print axioms YangMills.RG.PhysicalGaugeCMP116ActivityTransport.norm_gaussianRootMap_le
#print axioms YangMills.RG.PhysicalGaugeCMP116ActivityTransport.norm_gaussianRootMap_apply_le
#print axioms YangMills.RG.PhysicalGaugeCMP116ActivityTransport.ofDictionary
