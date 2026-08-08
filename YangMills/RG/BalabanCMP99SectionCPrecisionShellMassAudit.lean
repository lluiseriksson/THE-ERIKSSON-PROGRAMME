/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SectionCPrecisionShellMass

/-!
# Axiom audit: explicit precision-shell kernel mass
-/

#print axioms YangMills.RG.physicalCovarianceKernelBound_neg_weight
#print axioms YangMills.RG.physicalCovarianceKernelBound_add_weight
#print axioms YangMills.RG.physicalCovarianceKernelBound_projection_comp_projection_shell
#print axioms YangMills.RG.physicalCovarianceKernelBound_smul_shellProjection
#print axioms YangMills.RG.cmp99PrecisionShellExpansion_kernelBound
#print axioms YangMills.RG.cmp99LocalizedPhysicalPrecision_sub_kernelBound_shellMajorant
#print axioms YangMills.RG.sum_cmp99ShellCrossKernel_le_right
#print axioms YangMills.RG.sum_cmp99ShellCrossKernel_le_left
#print axioms YangMills.RG.sum_cmp99ShellDiagonalKernel_le
#print axioms YangMills.RG.cmp99PrecisionShellKernelMajorant_nonneg
#print axioms YangMills.RG.sum_cmp99PrecisionShellKernelMajorant_le
#print axioms YangMills.RG.cmp99SectionCCovarianceDifference_bilateralShellDecay_of_finiteRangeKernelBound
