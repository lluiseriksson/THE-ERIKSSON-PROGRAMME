/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PatchedParametrixSparseWalkBranching

/-! Axiom audit for volume-uniform sparse CMP99 walk branching. -/

#print axioms YangMills.RG.cmp99PhysicalPatchSuccessorSteps
#print axioms YangMills.RG.mem_cmp99PhysicalPatchSuccessorSteps_iff
#print axioms YangMills.RG.card_cmp99PhysicalPatchSuccessorSteps
#print axioms YangMills.RG.image_cmp99PhysicalPatchSuccessors_subset_meetingSimpleDomains
#print axioms YangMills.RG.card_cmp99PhysicalPatchSuccessors_le_simpleDomainBound
#print axioms YangMills.RG.card_cmp99PhysicalPatchSuccessorSteps_le_simpleDomainBound
#print axioms YangMills.RG.chain_of_mem_cmp99PhysicalPatchAdmissibleTails
#print axioms YangMills.RG.card_cmp99PhysicalPatchAdmissibleTails_le_pow_simpleDomainBound
