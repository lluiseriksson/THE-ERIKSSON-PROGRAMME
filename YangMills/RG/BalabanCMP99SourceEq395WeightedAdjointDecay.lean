/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395GlobalMiddleNorm
import YangMills.RG.BalabanCMP99SourceGeneratedWeightedAdjointRange

/-!
# Exponential kernel bound for the generated CMP99 weighted synthesis

The physical synthesis has exact terminal-block range and a
volume-independent counting norm.  This module combines the two facts into
a rectangular exponential kernel bound at any prescribed positive rate.
-/

namespace YangMills.RG
open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace
noncomputable section

variable {M Nc Q : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]

/-- The coordinate-exposed generated weighted synthesis is exponentially
localized with the exact terminal-block support cost. -/
theorem cmp99Eq395GeneratedPhysicalWeightedAdjoint_exponentialKernelBound
    (Omega : ActiveGaugeRegion 4 (2 * Q))
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon rate : ℝ} (hspacing : 0 < spacing) (hrate : 0 < rate)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) Omega (depth + 1)
    let W := regions.physicalWeightedAdjoint (show 2 ≤ 4 by norm_num) hM
      (matrixSUNAdjointModel Nc) spacing epsilon background
      budget.toRadiusChain fineSmall
    FinitePiLpTypedExponentialKernelBound W
      (fun target source => finBoxDist target.1
        (regions.terminalRepresentative source).1)
      (cmp99SourceGeneratedWeightedAdjointNormBound M depth *
        Real.exp (rate * ((M ^ (depth + 1) - 1 : ℕ) : ℝ)))
      rate := by
  dsimp only
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let W := regions.physicalWeightedAdjoint (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let beta := cmp99SourceGeneratedWeightedAdjointNormBound M depth
  let R := M ^ (depth + 1) - 1
  have hnormT :
      ‖(regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
        (matrixSUNAdjointModel Nc) spacing epsilon background
        budget.toRadiusChain fineSmall).weightedAdjoint‖ ≤ beta := by
    simpa [regions, beta] using
      norm_cmp99Eq395GeneratedWeightedAdjoint_le Omega hM depth hspacing
        background budget fineSmall
  have hnormW : ‖W‖ ≤ beta := by
    calc
      ‖W‖ =
          ‖(regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
            (matrixSUNAdjointModel Nc) spacing epsilon background
            budget.toRadiusChain fineSmall).weightedAdjoint‖ := by
        simpa [W] using regions.norm_physicalWeightedAdjoint
          (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
          spacing epsilon background budget.toRadiusChain fineSmall
      _ ≤ beta := hnormT
  have hbeta : 0 ≤ beta := (norm_nonneg W).trans hnormW
  have hrange : FinitePiLpTypedFiniteRange W
      (fun target source => finBoxDist target.1
        (regions.terminalRepresentative source).1) R := by
    simpa [regions, W, R] using
      cmp99SourceIteratedLift_physicalWeightedAdjoint_finiteRange
        (M := M) Omega (depth + 1) (show 2 ≤ 4 by norm_num) hM
        (matrixSUNAdjointModel Nc) spacing epsilon background
        budget.toRadiusChain fineSmall
  have hkernel : FinitePiLpTypedKernelBound W (fun _ _ => beta) := by
    intro source target v
    calc
      ‖W (singleFinitePiLp source v) target‖ ≤ ‖W‖ * ‖v‖ :=
        finitePiLpTypedKernelBound_const_opNorm W source target v
      _ ≤ beta * ‖v‖ :=
        mul_le_mul_of_nonneg_right hnormW (norm_nonneg v)
  simpa [W, beta, R] using
    finitePiLpTypedExponentialKernelBound_of_finiteRange
      hbeta hrate W hrange hkernel

end
end YangMills.RG
