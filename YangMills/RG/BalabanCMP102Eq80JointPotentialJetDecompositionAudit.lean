/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80JointPotentialJetDecomposition

/-!
# Axiom audit for the equation-(80) joint-jet decomposition
-/

#print axioms YangMills.RG.cmp102Eq80GlobalPotential_eq_jointTermSum
#print axioms YangMills.RG.contDiff_top_cmp102Eq80JointSourceTerm
#print axioms YangMills.RG.contDiff_top_cmp102Eq80JointTransportTerm
#print axioms YangMills.RG.contDiff_top_cmp102Eq80JointQuadraticTerm
#print axioms YangMills.RG.contDiff_top_cmp102Eq80JointRemainderTerm
#print axioms
  YangMills.RG.norm_iteratedFDeriv_cmp102Eq80JointPotential_le_componentJetMajorant
