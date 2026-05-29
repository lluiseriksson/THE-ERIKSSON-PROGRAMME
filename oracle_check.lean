import YangMillsCore

/-! Oracle check: every new core result must depend only on
`[propext, Classical.choice, Quot.sound]` — no `sorry`, no project axioms. -/

-- The two engines
#print axioms YangMills.haar_integral_eq_zero_of_center_eigenfunction
#print axioms YangMills.integral_eq_zero_of_left_invariant_eigenfunction

-- The Z_N selection rules
#print axioms YangMills.sunHaarProb_trace_pow_complex_integral_zero
#print axioms YangMills.sunHaarProb_trace_mixedPow_integral_zero
#print axioms YangMills.sunHaarProb_fundMonomial_integral_zero
#print axioms YangMills.sunHaarProb_tracematpow_integral_zero
#print axioms YangMills.sunHaarProb_tracematpow_mixed_integral_zero

-- SU(1) degeneracy and U(1) exact orthogonality
#print axioms YangMills.specialUnitaryGroup_fin_one_eq_one
#print axioms YangMills.integral_fourier_eq_indicator
#print axioms YangMills.integral_fourier_mul_conj_eq_indicator
