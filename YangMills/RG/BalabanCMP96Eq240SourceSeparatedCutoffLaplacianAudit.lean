import YangMills.RG.BalabanCMP96Eq240SourceSeparatedCutoffLaplacian

/-!
# Audit: cutoff-Laplacian species in CMP96 (2.40)

Cold GitHub Actions run `31047332477` verified all six declarations from
source checkpoint `972e8d115517c6f1f9bea97ec348bd0e31e1368d` with exactly
`[propext, Classical.choice, Quot.sound]`.
-/

#print axioms YangMills.RG.cmp96SourceSeparatedCutoffDifferenceBudget_nonneg
#print axioms YangMills.RG.norm_cmp96SourceSeparatedCutoff_sub_shift_le
#print axioms YangMills.RG.norm_cmp96SourceSeparatedCutoff_sub_shiftBack_le
#print axioms YangMills.RG.norm_cmp96SourceSeparatedCutoffLaplacianCoefficient_le
#print axioms YangMills.RG.cmp99CutoffLaplacianCorrection_one_eq_cmp96SourceSeparatedCoefficient
#print axioms YangMills.RG.cmp96SourceSeparatedCutoffLaplacianBudget_mul_generatedRange
