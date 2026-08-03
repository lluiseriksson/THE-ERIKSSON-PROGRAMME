import YangMills.RG.BalabanCMP99SourceRegionalGreenNeumann

/-!
# Axiom audit for the CMP99 regional Green Neumann reconstruction

PRE-VALIDATION: the revised fine-carrier audit has not yet been materialized
to `.olean`; its result is not compiler-verified.
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
