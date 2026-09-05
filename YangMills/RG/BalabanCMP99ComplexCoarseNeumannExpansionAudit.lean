/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99ComplexCoarseNeumannExpansion

/-!
# Axiom audit for the complex CMP99 coarse Neumann expansion
-/

#print axioms YangMills.RG.complexMatrixRelativeNeumannInverse
#print axioms YangMills.RG.mul_complexMatrixRelativeNeumannInverse_eq_one
#print axioms YangMills.RG.complexMatrixNonsingInv_eq_relativeNeumannInverse
#print axioms YangMills.RG.cmp99SourcePi4FullComplexCoarseMiddleMatrix_inv_eq_neumann
#print axioms YangMills.RG.cmp99SourcePi4ComplexBackgroundMinimizerNeumannLayer
#print axioms YangMills.RG.cmp99SourcePi4FullComplexBackgroundMinimizerMatrix_eq_tsum_neumannLayers
#print axioms YangMills.RG.cmp99SourcePi4FullComplexBackgroundMinimizerMatrix_eq_tsum_neumannLayers_of_source
