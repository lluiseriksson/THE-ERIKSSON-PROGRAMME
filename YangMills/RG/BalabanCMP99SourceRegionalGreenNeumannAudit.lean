import YangMills.RG.BalabanCMP99SourceRegionalGreenNeumann

/-!
# Axiom audit for the CMP99 regional Green Neumann reconstruction

Compiler-verified at source checkpoint
`837040284f5ce1d358d42eb8f6c01689829db29b` in durable GitHub Actions run
`30971247380`; all eleven declarations use exactly
`[propext, Classical.choice, Quot.sound]`.
-/

#print axioms YangMills.RG.isCoerciveCLM_cmp99RegionalDirichletPrecision
#print axioms YangMills.RG.cmp99RegionalDirichletPrecision_comp_green
#print axioms YangMills.RG.CMP99RegionalSquarePartitionHasFiniteRangeMargin
#print axioms YangMills.RG.cmp99RegionalSquarePartitionSupported_of_finiteRangeMargin
#print axioms YangMills.RG.cmp99RegionalSquareMultiplier_comp_regionProjector
#print axioms YangMills.RG.cmp99RegionalSquareMultiplier_precision_green_eq_sq
#print axioms YangMills.RG.comp_cmp99RegionalGreenHead_eq_sq_sub_correction
#print axioms YangMills.RG.comp_cmp99RegionalGreenParametrix_eq_id_sub_defect
#print axioms YangMills.RG.cmp99RegionalGreenNeumann_eq_parametrix_comp_tsum_pow
#print axioms YangMills.RG.comp_cmp99RegionalGreenNeumann_eq_id
#print axioms YangMills.RG.cmp99RegionalGreenNeumann_eq_ambientGreen
