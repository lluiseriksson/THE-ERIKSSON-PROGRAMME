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
