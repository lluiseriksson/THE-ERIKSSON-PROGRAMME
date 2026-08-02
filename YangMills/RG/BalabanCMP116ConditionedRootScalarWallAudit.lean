/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ConditionedRootScalarWall

/-!
# Audit: conditioned-root scalar wall

Validated in a fresh Colab CPU/high-RAM clone at source checkpoint
`4cf34623cf6096f89653cd9fb1c3dc848a7e9294`; all declarations below used
exactly `[propext, Classical.choice, Quot.sound]`.

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
