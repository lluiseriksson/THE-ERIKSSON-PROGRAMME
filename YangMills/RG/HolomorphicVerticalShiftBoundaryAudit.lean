/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.HolomorphicVerticalShiftBoundary

/-!
# Axiom audit for the boundary-seam vertical contour shift

PRE-VALIDATION: source is present; its `.olean` has not yet been materialized,
and the result is not yet compiler-verified.
-/

#print axioms YangMills.RG.intervalIntegral_eq_verticalShift_of_boundary_eq_of_differentiableOn
