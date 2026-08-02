/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP109ConstraintCorrectionParameterFamily

/-!
# Oracle audit for the parameter-uniform CMP109 correction

PRE-VALIDATION: the source is present, its `.olean` has not yet been
materialized, and the audit is not yet compiler-verified.
-/

#print axioms YangMills.RG.CMP109ConstraintCorrectionParameterFamilyData.contractionRate_lt_one
#print axioms YangMills.RG.CMP109ConstraintCorrectionParameterFamilyData.correction_mem_ball
#print axioms YangMills.RG.CMP109ConstraintCorrectionParameterFamilyData.correction_fixedPoint
#print axioms YangMills.RG.CMP109ConstraintCorrectionParameterFamilyData.correction_physicalEquation
