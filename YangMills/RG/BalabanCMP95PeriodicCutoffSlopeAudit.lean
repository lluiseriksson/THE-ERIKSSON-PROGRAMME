import YangMills.RG.BalabanCMP95PeriodicCutoffSlope

/-!
# Axiom audit for the linear periodic-cutoff slope

Compiler-verified at source checkpoint
`837040284f5ce1d358d42eb8f6c01689829db29b` in durable GitHub Actions run
`30971247380`; all eight declarations use exactly
`[propext, Classical.choice, Quot.sound]`.
-/

#print axioms YangMills.RG.cmp95PeriodicCutoff_nonneg
#print axioms YangMills.RG.norm_cmp95PeriodicCutoff_le_one
#print axioms YangMills.RG.norm_cmp95PeriodicCutoff_sub_le
#print axioms YangMills.RG.norm_cmp95RescaledPeriodicCutoff_sub_le
#print axioms YangMills.RG.cmp95RescaledPeriodicCutoff_add_period
#print axioms YangMills.RG.cmp95RescaledPeriodicTensorCutoff_eq_prod
#print axioms YangMills.RG.norm_cmp95RescaledPeriodicTensorCutoff_finBox_sub_le
#print axioms YangMills.RG.norm_cmp99SourceGeneratedFineCellCutoff_finBox_sub_le
