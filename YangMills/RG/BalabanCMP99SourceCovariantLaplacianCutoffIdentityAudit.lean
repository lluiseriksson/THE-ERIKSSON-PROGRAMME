/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceCovariantLaplacianCutoffIdentity

/-!
# Audit: covariant-Laplacian terms in CMP99 (3.88)

Compiler-verified from exact source checkpoint
`767f54dd847b2459f05b2e2a9ea5ac320b8ccd35` in cold GitHub Actions run
`30984221871`.  All four declarations below use exactly
`[propext, Classical.choice, Quot.sound]`.
-/

#print axioms YangMills.RG.cmp99_covariant_cutoff_product_rule_direction
#print axioms YangMills.RG.cmp99GeneratedAmbientScaledCovariantLaplacian_apply_eq_stencil
#print axioms YangMills.RG.cmp99AmbientCovariantLaplacianStencil_scalarMultiplier
#print axioms YangMills.RG.cmp99GeneratedAmbientScaledCovariantLaplacian_scalarMultiplier
