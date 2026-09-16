/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedCanonicalTerminalRestriction
import YangMills.RG.BalabanCMP99SourceGeneratedLaplacianTransitionSupport

/-!
# Adjoint of physical restriction between nested CMP99 source regions

The terminal rectangular defect is oriented from the large source region to
the small one.  Its Hilbert adjoint must therefore be literal zero extension
in the reverse direction.  This file records that identity without an
abstract synthesis map.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d N : ℕ} [NeZero N]

/-- Zero extension from the smaller active region into the larger one,
written on the same physical regional Hilbert spaces as nested restriction.
-/
noncomputable def cmp99NestedActiveRegionExtension
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (OmegaSmall OmegaLarge : ActiveGaugeRegion d N) :
    ActiveGaugeZeroCochain OmegaSmall g →L[ℝ]
      ActiveGaugeZeroCochain OmegaLarge g :=
  (restrictZeroCLM OmegaLarge).comp (extendZeroZeroCLM OmegaSmall)

/-- The counting-Hilbert adjoint of literal nested restriction is literal
zero extension in the reverse direction. -/
theorem cmp99NestedActiveRegionRestriction_adjoint_eq_extension
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (OmegaSmall OmegaLarge : ActiveGaugeRegion d N) :
    (cmp99NestedActiveRegionRestriction (g := g)
      OmegaSmall OmegaLarge).adjoint =
      cmp99NestedActiveRegionExtension (g := g) OmegaSmall OmegaLarge := by
  rw [cmp99NestedActiveRegionRestriction,
    cmp99NestedActiveRegionExtension, ContinuousLinearMap.adjoint_comp]
  rw [cmp99ActiveRegion_restrictZero_eq_extendZero_adjoint OmegaLarge]
  rw [cmp99ActiveRegion_restrictZero_eq_extendZero_adjoint OmegaSmall]
  rw [ContinuousLinearMap.adjoint_adjoint]

end

end YangMills.RG
