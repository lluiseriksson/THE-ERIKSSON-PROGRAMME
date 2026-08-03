import YangMills.RG.BalabanCMP95PeriodicCutoffSlope

/-!
# Axiom audit for the linear periodic-cutoff slope

PRE-VALIDATION: this audit has not yet been materialized to `.olean`; its
result is not compiler-verified.
-/

#print axioms YangMills.RG.cmp95PeriodicCutoff_nonneg
#print axioms YangMills.RG.norm_cmp95PeriodicCutoff_le_one
#print axioms YangMills.RG.norm_cmp95PeriodicCutoff_sub_le
#print axioms YangMills.RG.norm_cmp95RescaledPeriodicCutoff_sub_le
#print axioms YangMills.RG.cmp95RescaledPeriodicCutoff_add_period
#print axioms YangMills.RG.cmp95RescaledPeriodicTensorCutoff_eq_prod
#print axioms YangMills.RG.norm_cmp95RescaledPeriodicTensorCutoff_finBox_sub_le
#print axioms YangMills.RG.norm_cmp99SourceGeneratedFineCellCutoff_finBox_sub_le
