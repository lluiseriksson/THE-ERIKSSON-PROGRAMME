/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80JointQuadraticTermJetBound

/-!
# Axiom audit for the equation-(80) quadratic-term jet bound
-/

#print axioms
  YangMills.RG.cmp102Eq80JointEvaluationJetMajorant_nonneg
#print axioms
  YangMills.RG.norm_iteratedFDeriv_cmp102Eq80JointEvaluation_le
#print axioms
  YangMills.RG.norm_iteratedFDeriv_cmp102Eq80JointQuadraticTerm_le
