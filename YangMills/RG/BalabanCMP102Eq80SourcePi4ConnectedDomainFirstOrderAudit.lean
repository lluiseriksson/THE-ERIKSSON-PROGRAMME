/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4ConnectedDomainFirstOrder

#print axioms
  YangMills.RG.iteratedFDeriv_propagatorSlice_eq_partialPropagatorJet
#print axioms YangMills.RG.fderiv_cmp102PartialPropagatorJet
#print axioms
  YangMills.RG.hasFDerivAt_cmp102PartialPropagatorJet_zero
#print axioms YangMills.RG.contDiff_cmp102Eq80JointPotential
#print axioms
  YangMills.RG.fderiv_cmp102Eq80JointPotential_vertical_zero
#print axioms
  YangMills.RG.cmp102Eq80SourcePi4FaaDiBrunoDomainChoiceTermAt_hasFDerivAt_zero_field
#print axioms
  YangMills.RG.cmp102Eq80SourcePi4FaaDiBrunoPartitionDomainCoefficientAt_hasFDerivAt_zero_field
#print axioms
  YangMills.RG.cmp102Eq80SourcePi4FaaDiBrunoDomainCoefficientAt_hasFDerivAt_zero_field
