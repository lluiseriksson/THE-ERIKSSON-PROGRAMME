import YangMills.RG.BalabanCMP85TypedGreenInverse



/-!
axiom audit for the typed P3 Green inverse.

PRE-VALIDATION: this module's source is present, its `.olean` has not yet
been materialized, and its result has not yet been verified by the compiler.
-/

open YangMills.RG

#print axioms YangMills.RG.cmp85TypedFinePrecision
#print axioms YangMills.RG.cmp85TypedNextPrecision
#print axioms YangMills.RG.cmp85TypedGreenCandidate
#print axioms YangMills.RG.cmp85TypedNextPrecision_eq_fine_add_error
#print axioms YangMills.RG.cmp85TypedGreenCandidate_rightInverse
#print axioms YangMills.RG.cmp85TypedGreenCandidate_leftInverse
#print axioms YangMills.RG.cmp85TypedGreen_eq_candidate
#print axioms YangMills.RG.cmp85Typed_averagedGreenRecurrence
