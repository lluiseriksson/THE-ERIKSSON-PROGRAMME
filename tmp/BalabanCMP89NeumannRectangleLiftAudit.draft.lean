import YangMills.RG.BalabanCMP89NeumannRectangleLift

/-!
# Draft axiom audit: exact complete-block lift of the CMP89 rectangle

This draft is deliberately outside the import graph. It may be promoted only
after the base rectangular active region has cold compiler evidence and the
lift module has been promoted under its PRE-VALIDATION marker.
-/

namespace YangMills.RG

#print axioms cmp89SourceNeumannScaleRectangleSide
#print axioms cmp89SourceNeumannScaleRectangleSidePow
#print axioms cmp99LiftActiveRegion_cmp89Rectangle_eq
#print axioms cmp99IteratedLiftActiveRegion_cmp89Rectangle_eq
#print axioms cmp89SourceNeumannIteratedLiftedRectangleSiteEquiv
#print axioms cmp89SourceNeumannLiftedRectangleSiteEquiv

end YangMills.RG
