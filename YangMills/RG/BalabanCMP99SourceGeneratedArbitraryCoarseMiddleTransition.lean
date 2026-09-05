/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedCoarseCovarianceTransition

/-!
# Arbitrary nested-region transition of the generated CMP99 middle

The source proof of equation (3.95) compares the global middle on the full
coarse torus with a regional middle on `Pi^4`.  This is not one of the
consecutive transitions in the local `Omega` sequence.  The generated
`Q'` tower already intertwines arbitrary nested source regions, so this file
keeps that inclusion literal and transports the complete middle defect to
the corresponding rectangular Green mismatch.

No decay estimate for that mismatch is assumed or claimed here.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {Q M Nc : ℕ} [NeZero Q] [NeZero M] [NeZero Nc]

/-- Literal rectangular Green mismatch for arbitrary nested generated
source regions. -/
noncomputable def cmp99SourceGeneratedNestedPhysicalGreenTransition
    (OmegaSmall OmegaLarge : ActiveGaugeRegion 4 (2 * Q))
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :=
  let Gsmall := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
    OmegaSmall depth hspacing background budget fineSmall hsmall
  let Glarge := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
    OmegaLarge depth hspacing background budget fineSmall hsmall
  let R := cmp99NestedActiveRegionRestriction (g := SUNLieCoord Nc)
    (cmp99IteratedLiftActiveRegion (M := M) OmegaSmall (depth + 1))
    (cmp99IteratedLiftActiveRegion (M := M) OmegaLarge (depth + 1))
  Gsmall.comp R - R.comp Glarge

/-- For arbitrary nested source regions, the complete generated mass drops
out of the rectangular precision defect. -/
theorem cmp99SourceGeneratedNestedPhysicalPrecisionDefect_eq_laplacianDefect
    (OmegaSmall OmegaLarge : ActiveGaugeRegion 4 (2 * Q))
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
    (hM : 2 ≤ M) (depth : ℕ) (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let FineSmall := cmp99IteratedLiftActiveRegion (M := M) OmegaSmall
      (depth + 1)
    let FineLarge := cmp99IteratedLiftActiveRegion (M := M) OmegaLarge
      (depth + 1)
    let R := cmp99NestedActiveRegionRestriction (g := SUNLieCoord Nc)
      FineSmall FineLarge
    cmp99TypedPrecisionDefect
        (cmp99SourceGeneratedPhysicalPrecision (show 2 ≤ 4 by norm_num) hM
          OmegaLarge depth spacing epsilon background budget fineSmall)
        (cmp99SourceGeneratedPhysicalPrecision (show 2 ≤ 4 by norm_num) hM
          OmegaSmall depth spacing epsilon background budget fineSmall) R =
      cmp99TypedPrecisionDefect
        (cmp99ActiveRegionSourceCovariantLaplacian FineLarge
          (matrixSUNAdjointModel Nc) background spacing)
        (cmp99ActiveRegionSourceCovariantLaplacian FineSmall
          (matrixSUNAdjointModel Nc) background spacing) R := by
  rw [cmp99SourceGeneratedPhysicalPrecision,
    cmp99SourceGeneratedPhysicalPrecision,
    cmp99SourceGaugePrecision, cmp99SourceGaugePrecision]
  exact cmp99TypedPrecisionDefect_add_mass_eq _ _ _ _ _ _
    (cmp99SourceIteratedLift_QprimeMass_transition hsub
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) (depth + 1)
      spacing epsilon background budget.toRadiusChain fineSmall)

/-- Exact arbitrary nested-region second-resolvent identity. -/
theorem cmp99SourceGeneratedNestedPhysicalGreen_transition_resolvent
    (OmegaSmall OmegaLarge : ActiveGaugeRegion 4 (2 * Q))
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    let Gsmall := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
      OmegaSmall depth hspacing background budget fineSmall hsmall
    let Glarge := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
      OmegaLarge depth hspacing background budget fineSmall hsmall
    let R := cmp99NestedActiveRegionRestriction (g := SUNLieCoord Nc)
      (cmp99IteratedLiftActiveRegion (M := M) OmegaSmall (depth + 1))
      (cmp99IteratedLiftActiveRegion (M := M) OmegaLarge (depth + 1))
    let Ddef := cmp99TypedPrecisionDefect
      (cmp99SourceGeneratedPhysicalPrecision (show 2 ≤ 4 by norm_num) hM
        OmegaLarge depth spacing epsilon background budget fineSmall)
      (cmp99SourceGeneratedPhysicalPrecision (show 2 ≤ 4 by norm_num) hM
        OmegaSmall depth spacing epsilon background budget fineSmall) R
    cmp99SourceGeneratedNestedPhysicalGreenTransition OmegaSmall OmegaLarge hM
        depth hspacing background budget fineSmall hsmall =
      Gsmall.comp (Ddef.comp Glarge) := by
  unfold cmp99SourceGeneratedNestedPhysicalGreenTransition
  exact typedGreen_transition_resolvent _ _ _ _ _
    (cmp99SourceGeneratedPhysicalPrecision_comp_green
      (show 2 ≤ 4 by norm_num) hM OmegaLarge depth hspacing background
      budget fineSmall hsmall)
    (cmp99SourceGeneratedPhysicalGreen_comp_precision
      (show 2 ≤ 4 by norm_num) hM OmegaSmall depth hspacing background
      budget fineSmall hsmall)

/-- Rectangular defect of the generated middle operators attached to two
arbitrary nested coarse source regions. -/
noncomputable def cmp99SourceGeneratedNestedCoarseMiddleDefect
    (OmegaSmall OmegaLarge : ActiveGaugeRegion 4 (2 * Q))
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :=
  let regionsSmall := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    OmegaSmall (depth + 1)
  let regionsLarge := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    OmegaLarge (depth + 1)
  let Tsmall := regionsSmall.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let Tlarge := regionsLarge.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  cmp99TypedPrecisionDefect
    (cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
      (show 2 ≤ 4 by norm_num) hM OmegaLarge depth hspacing background
      budget fineSmall hsmall)
    (cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
      (show 2 ≤ 4 by norm_num) hM OmegaSmall depth hspacing background
      budget fineSmall hsmall)
    (cmp99SourceIteratedLiftTerminalRestriction hsub (show 2 ≤ 4 by norm_num)
      hM (matrixSUNAdjointModel Nc) (depth + 1) spacing epsilon background
      budget.toRadiusChain fineSmall)

/-- Complete `Q'` transport of the rectangular Green mismatch for arbitrary
nested source regions. -/
noncomputable def cmp99SourceGeneratedNestedCoarseMiddleGreenTransport
    (OmegaSmall OmegaLarge : ActiveGaugeRegion 4 (2 * Q))
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :=
  let regionsSmall := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    OmegaSmall (depth + 1)
  let regionsLarge := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    OmegaLarge (depth + 1)
  let Tsmall := regionsSmall.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let Tlarge := regionsLarge.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let Gsmall := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
    OmegaSmall depth hspacing background budget fineSmall hsmall
  let Glarge := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
    OmegaLarge depth hspacing background budget fineSmall hsmall
  let Rfine := cmp99NestedActiveRegionRestriction (g := SUNLieCoord Nc)
    (cmp99IteratedLiftActiveRegion (M := M) OmegaSmall (depth + 1))
    (cmp99IteratedLiftActiveRegion (M := M) OmegaLarge (depth + 1))
  let H := (Gsmall.comp (Gsmall.comp Rfine - Rfine.comp Glarge)) +
    ((Gsmall.comp Rfine - Rfine.comp Glarge).comp Glarge)
  show Tlarge.TerminalSpace.carrier →L[ℝ]
      Tsmall.TerminalSpace.carrier from
    -(Tsmall.Qprime.comp (H.comp Tlarge.weightedAdjoint))

/- Transparent form of the generated middle operator on an arbitrary
source region. -/
theorem cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle_eq_Qprime_green_sq_arbitrary
    (Omega : ActiveGaugeRegion 4 (2 * Q))
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M)
      Omega (depth + 1)
    let T := regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
      (matrixSUNAdjointModel Nc) spacing epsilon background
      budget.toRadiusChain fineSmall
    let G := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
      Omega depth hspacing background budget fineSmall hsmall
    cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
        (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
        fineSmall hsmall =
      T.Qprime.comp (G.comp (G.comp T.weightedAdjoint)) := by
  rfl

/- Exact arbitrary-region reduction of the middle defect to the Green
mismatch.  In particular this applies to `Pi^4 ⊆ univ`, unlike the older
endpoint restricted to consecutive members of the local `Omega` sequence. -/
set_option maxHeartbeats 2000000 in
theorem cmp99SourceGeneratedNestedCoarseMiddleDefect_eq_greenMismatch
    (OmegaSmall OmegaLarge : ActiveGaugeRegion 4 (2 * Q))
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    cmp99SourceGeneratedNestedCoarseMiddleDefect OmegaSmall OmegaLarge hsub
        hM depth hspacing background budget fineSmall hsmall =
      cmp99SourceGeneratedNestedCoarseMiddleGreenTransport OmegaSmall OmegaLarge
        hM depth hspacing background budget fineSmall hsmall := by
  unfold cmp99SourceGeneratedNestedCoarseMiddleDefect
  unfold cmp99SourceGeneratedNestedCoarseMiddleGreenTransport
  rw [cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle_eq_Qprime_green_sq_arbitrary,
    cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle_eq_Qprime_green_sq_arbitrary]
  apply typedCoarseMiddleDefect_eq_greenMismatch
  · exact cmp99SourceIteratedLift_Qprime_transition hsub
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) (depth + 1)
      spacing epsilon background budget.toRadiusChain fineSmall
  · exact cmp99SourceIteratedLift_weightedAdjoint_transition hsub
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) (depth + 1)
      spacing epsilon background budget.toRadiusChain fineSmall

end

end YangMills.RG
