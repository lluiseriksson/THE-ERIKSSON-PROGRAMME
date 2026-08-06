/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP95SourceSmoothPartitionSecondDerivative

/-!
# Audit: derived CMP95 second-derivative budget

Compiler-verified at exact source checkpoint
`aaafae326ab952d990c0efb6a66553f0d2a61add` by cold GitHub Actions run
`31067778196`.
-/

#print axioms YangMills.RG.CMP95SourceSmoothPartitionProfile.hasCompactSupport
#print axioms YangMills.RG.CMP95SourceSmoothPartitionProfile.exists_secondDerivBound
#print axioms YangMills.RG.CMP95SourceSmoothPartitionProfile.secondDerivBound_nonneg
#print axioms YangMills.RG.CMP95SourceSmoothPartitionProfile.norm_iteratedDeriv_two_le_secondDerivBound
