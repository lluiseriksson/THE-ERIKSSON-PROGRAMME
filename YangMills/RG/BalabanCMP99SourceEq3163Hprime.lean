/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395CanonicalCovariance

/-!
# The literal CMP99 equation (3.163) background-field operator

After adjoining the last source region, CMP99 determines the translated
field `lambda_0 = H' mu` by

`G'^2 Q'^* (Q' G'^2 Q'^*)^-1 (1 - a Q' G' Q'^*) mu
  + a G' Q'^* mu`.

This file constructs that operator from the generated physical Green
operator, the weighted source adjoint, and the canonical covariance already
identified with the exhaustive equation (3.95) Neumann sum.  Its decisive
source constraint `Q' H' = 1` is proved exactly.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Literal operator on the right-hand side of CMP99 equation (3.163). -/
noncomputable def cmp99SourceEq3163PhysicalHprime
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M (depth + 1)
      spacing epsilon < 1) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) Omega (depth + 1)
    let T := regions.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
      spacing epsilon background budget.toRadiusChain fineSmall
    T.TerminalSpace.carrier →L[ℝ]
      ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
        (SUNLieCoord Nc) := by
  dsimp only
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let T := regions.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
    spacing epsilon background budget.toRadiusChain fineSmall
  let G := cmp99SourceGeneratedPhysicalGreen hd hM Omega depth hspacing
    background budget fineSmall hsmall
  let C := cmp99SourceGeneratedPhysicalCoarseCovariance hd hM Omega depth
    hspacing background budget fineSmall hsmall
  let a := cmp99SourceGeneratedPhysicalMass d M (depth + 1) spacing epsilon
  exact
    (G.comp (G.comp (T.weightedAdjoint.comp
      (C.comp (ContinuousLinearMap.id ℝ _ -
        a • T.Qprime.comp (G.comp T.weightedAdjoint)))))) +
      a • G.comp T.weightedAdjoint

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
/-- The field produced by equation (3.163) has exactly the prescribed final
block average: `Q' (H' mu) = mu`. -/
theorem cmp99SourceEq3163_Qprime_comp_physicalHprime_eq_id
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M (depth + 1)
      spacing epsilon < 1) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) Omega (depth + 1)
    let T := regions.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
      spacing epsilon background budget.toRadiusChain fineSmall
    T.Qprime.comp
      (cmp99SourceEq3163PhysicalHprime hd hM Omega depth hspacing background
        budget fineSmall hsmall) =
      ContinuousLinearMap.id ℝ T.TerminalSpace.carrier := by
  dsimp only
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let T := regions.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
    spacing epsilon background budget.toRadiusChain fineSmall
  let G := cmp99SourceGeneratedPhysicalGreen hd hM Omega depth hspacing
    background budget fineSmall hsmall
  let C := cmp99SourceGeneratedPhysicalCoarseCovariance hd hM Omega depth
    hspacing background budget fineSmall hsmall
  let a := cmp99SourceGeneratedPhysicalMass d M (depth + 1) spacing epsilon
  let Middle := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle hd hM Omega
    depth hspacing background budget fineSmall hsmall
  have hMiddle : Middle = T.Qprime.comp (G.comp (G.comp T.weightedAdjoint)) := rfl
  have hMC : Middle.comp C = ContinuousLinearMap.id ℝ _ :=
    cmp99SourceGeneratedPhysicalCoarseCovariance_middle_comp hd hM Omega depth
      hspacing background budget fineSmall hsmall
  unfold cmp99SourceEq3163PhysicalHprime
  change T.Qprime.comp
      ((G.comp (G.comp (T.weightedAdjoint.comp
        (C.comp (ContinuousLinearMap.id ℝ _ -
          a • T.Qprime.comp (G.comp T.weightedAdjoint)))))) +
        a • G.comp T.weightedAdjoint) = _
  rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul]
  rw [show T.Qprime.comp
      (G.comp (G.comp (T.weightedAdjoint.comp
        (C.comp (ContinuousLinearMap.id ℝ _ -
          a • T.Qprime.comp (G.comp T.weightedAdjoint)))))) =
      (Middle.comp C).comp (ContinuousLinearMap.id ℝ _ -
        a • T.Qprime.comp (G.comp T.weightedAdjoint)) by
        simp only [ContinuousLinearMap.comp_assoc, hMiddle]]
  rw [hMC, ContinuousLinearMap.id_comp]
  module

end

end YangMills.RG
