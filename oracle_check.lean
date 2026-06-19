import YangMillsCore

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
-- the free RG step's covariance transformation law (on Mathlib's IsGaussian)
#print axioms YangMills.RG.covarianceBilinDual_map_clm

/-! ### The near-identity matrix-logarithm calculus -/
-- the quantitative axiom (0.8): exp(nearLog Y) = 1 + Y + O(‖Y‖²)
#print axioms YangMills.RG.norm_exp_nearLog_sub_one_sub_self_le
-- scalar correctness (non-vacuity: nearLog IS the logarithm) + conjugation-equivariance
#print axioms YangMills.RG.nearLog_real
#print axioms YangMills.RG.nearLog_conj

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
#print axioms YangMills.RG.holePolymerSystem_converges_volumeUniform
#print axioms YangMills.RG.holePolymerSystem_norm_clusterSum_le_volumeUniform

#print axioms YangMills.RG.clusterUnion
#print axioms YangMills.RG.clusterModifiedMetric
#print axioms YangMills.RG.clusterUnion_skeleton
#print axioms YangMills.RG.clusterUnion_fin_one
#print axioms YangMills.RG.clusterModifiedMetric_fin_one
#print axioms YangMills.RG.clusterDecayWeight
#print axioms YangMills.RG.clusterDecayWeight_fin_one
#print axioms YangMills.RG.walkConnected_union
#print axioms YangMills.RG.walk_union_connected
#print axioms YangMills.RG.cluster_closedNeigh_union_connected
#print axioms YangMills.RG.clusterRemainderSum_summable
#print axioms YangMills.RG.discreteModifiedMetric_le_clusterModifiedMetric
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


