/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ConditionedRootScalarWall

/-!
# Audit: conditioned-root scalar wall

PRE-VALIDATION: this source is present, its `.olean` has not yet been
materialized, and its results have not yet been verified by the Lean compiler.

The oracle gate below is intentionally colocated with the universal scalar
reduction.  It does not audit the still-missing physical compression theorem.
-/

namespace YangMills.RG

#print axioms norm_conditionedRoot_sq_eq_covariance
#print axioms mul_conditionedRoot_norm_sq_lt_one_of_lt_coercivity
#print axioms cmp116Eq225SourceCoefficient_le_inv_two_mul_coercivity_sub
#print axioms cmp116Eq226_optimalCovarianceSmall_of_conditionedCovarianceNorm
#print axioms cmp116Eq226_optimalGaussianSmall_of_conditionedCovarianceNorm

end YangMills.RG
