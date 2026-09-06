import YangMills.RG.NeumannInternalBondStencil

/-! Four-name production audit verified in a fresh cold clone at
81f35765ad50f8217bca20bc4530d99b3bf05103, ledger1166. Exact HOT body promotion
from ledger1165; no regional inverse or window15 is asserted. -/

#print axioms YangMills.RG.neumannInternalBond_restrict_eq_extend_adjoint
#print axioms YangMills.RG.neumannInternalBond_derivative_eq_restrict
#print axioms YangMills.RG.neumannInternalBond_adjoint_eq_extended_divergence
#print axioms YangMills.RG.neumannInternalBond_laplacian_apply
