/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116LocalizedCovarianceCompression

/-!
# Axiom audit for localized covariance compression

Validated from a fresh Colab high-RAM CPU clone at source SHA
`f04b5cb9937b12ca412ab21be5e1c35780c01836`: all six oracle outputs below
were restricted to `{propext, Classical.choice, Quot.sound}`.  Evidence
SHA-256:
`eb474ba299c08ba24d105b66a612eb6b1b93a92236bac1a45ce682d8980d68c3`.
-/

#print axioms YangMills.RG.cmp116Eq223CoordinateProjection_transpose
#print axioms YangMills.RG.norm_cmp116Eq223CoordinateProjection_le_one
#print axioms YangMills.RG.norm_cmp116LocalizedCovarianceCompression_le
#print axioms YangMills.RG.cmp116LocalizedCovarianceCompression_supported
#print axioms YangMills.RG.cmp116LocalizedCovarianceCompression_posSemidef
#print axioms YangMills.RG.cmp116LocalizedCovarianceRoot_certificate
