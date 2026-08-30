import YangMills.RG.BalabanCMP89SourceNeumannRegionalGaugePrecision

/-!
# Axiom audit for the CMP89 regional Neumann gauge precision

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and no result in this audit module is compiler-verified.
-/

namespace YangMills.RG

#print axioms inner_cmp89SourceNeumannRegionalGaugePrecision
#print axioms cmp89SourceNeumannRegionalGaugePrecision_isSymmetric
#print axioms isCoerciveCLM_cmp89SourceNeumannRegionalGaugePrecision
#print axioms cmp89SourceNeumannRegionalGaugePrecision_comp_green
#print axioms cmp89SourceNeumannRegionalGreen_comp_gaugePrecision

end YangMills.RG
