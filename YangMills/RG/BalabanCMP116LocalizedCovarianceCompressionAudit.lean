/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116LocalizedCovarianceCompression

/-!
# Axiom audit for localized covariance compression

PRE-VALIDATION: this source is present, its `.olean` has not yet been
materialized, and none of the oracle outputs below is compiler-verified.
-/

#print axioms YangMills.RG.cmp116Eq223CoordinateProjection_transpose
#print axioms YangMills.RG.norm_cmp116Eq223CoordinateProjection_le_one
#print axioms YangMills.RG.norm_cmp116LocalizedCovarianceCompression_le
#print axioms YangMills.RG.cmp116LocalizedCovarianceCompression_supported
#print axioms YangMills.RG.cmp116LocalizedCovarianceCompression_posSemidef
#print axioms YangMills.RG.cmp116LocalizedCovarianceRoot_certificate
