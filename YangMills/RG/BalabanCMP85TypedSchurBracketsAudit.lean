import YangMills.RG.BalabanCMP85TypedSchurBrackets



/-!
axiom audit for the typed P3 Schur layer.

PRE-VALIDATION: this module's source is present, its `.olean` has not yet
been materialized, and its result has not yet been verified by the compiler.
-/

open YangMills.RG

#print axioms YangMills.RG.cmp85TypedStepProjector
#print axioms YangMills.RG.cmp85TypedGreenSandwich
#print axioms YangMills.RG.cmp85TypedSchurPrecision
#print axioms YangMills.RG.cmp85TypedStepProjector_idempotent
#print axioms YangMills.RG.cmp85TypedStepProjector_absorb_left
#print axioms YangMills.RG.cmp85Typed_rightSchurBracket_eq_zero
#print axioms YangMills.RG.cmp85Typed_leftSchurBracket_eq_zero
#print axioms YangMills.RG.cmp85Typed_rightAveragingIdentity
