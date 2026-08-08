/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395LocalizedAtomSupport
import YangMills.RG.BalabanCMP99SourceGeneratedSectionCRightFactorNorm

/-!
# Uniform norm of the global middle in CMP99 equation (3.95)

The middle `Q' (G')^2 Q'^*` admits the same source-generated norm estimate
on every active region.  This file proves that statement without a regional
diameter hypothesis and transports it to the full coarse torus used in the
exhaustive equation (3.95) atom expansion.  The bound is independent of the
ambient volume.
-/

namespace YangMills.RG
open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace
noncomputable section

variable {M Nc Q : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]

/-- The generated weighted synthesis has its exact four-dimensional norm
cost on an arbitrary active region. -/
theorem norm_cmp99Eq395GeneratedWeightedAdjoint_le
    (Omega : ActiveGaugeRegion 4 (2 * Q))
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M)
      Omega (depth + 1)
    let T := regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
      (matrixSUNAdjointModel Nc) spacing epsilon background
      budget.toRadiusChain fineSmall
    ‖T.weightedAdjoint‖ ≤
      cmp99SourceGeneratedWeightedAdjointNormBound M depth := by
  dsimp only
  let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    Omega (depth + 1)
  let T := regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  apply ContinuousLinearMap.opNorm_le_bound _ (by
    unfold cmp99SourceGeneratedWeightedAdjointNormBound
    positivity)
  intro eta
  have hterminal : T.terminalSpacing =
      (M : ℝ) ^ (depth + 1) * spacing :=
    regions.weightedQprimeTower_terminalSpacing (show 2 ≤ 4 by norm_num) hM
      (matrixSUNAdjointModel Nc) spacing epsilon background
      budget.toRadiusChain fineSmall
  have hsq := T.weightedAdjoint_spacingNormSq eta
  rw [hterminal] at hsq
  have hspacing4 : 0 < spacing ^ 4 := pow_pos hspacing _
  have heq : ‖T.weightedAdjoint eta‖ ^ 2 =
      ((M : ℝ) ^ (2 * (depth + 1)) * ‖eta‖) ^ 2 := by
    have hpow : ((M : ℝ) ^ (depth + 1) * spacing) ^ 4 =
        spacing ^ 4 * ((M : ℝ) ^ (2 * (depth + 1))) ^ 2 := by ring
    rw [hpow] at hsq
    nlinarith
  apply le_of_sq_le_sq
  · exact heq.le
  · exact mul_nonneg (pow_nonneg (Nat.cast_nonneg M) _)
      (norm_nonneg eta)

/-- Uniform norm of the generated middle on an arbitrary active region. -/
theorem norm_cmp99Eq395GeneratedMiddle_le
    (Omega : ActiveGaugeRegion 4 (2 * Q))
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    ‖cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
        (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
          fineSmall hsmall‖ ≤
      (1 / cmp99SourceGeneratedCoercivity 4 M (depth + 1)
          spacing epsilon) ^ 2 *
        cmp99SourceGeneratedWeightedAdjointNormBound M depth := by
  let regions := cmp99SourceIteratedLiftActiveRegionChain (M := M)
    Omega (depth + 1)
  let T := regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let G := cmp99SourceGeneratedPhysicalGreen (show 2 ≤ 4 by norm_num) hM
    Omega depth hspacing background budget fineSmall hsmall
  let c := cmp99SourceGeneratedCoercivity 4 M (depth + 1) spacing epsilon
  have hc : 0 < c := cmp99SourceGeneratedCoercivity_pos 4 M depth hspacing hsmall
  have hQ : ‖T.Qprime‖ ≤ 1 :=
    regions.norm_weightedQprimeTower_Qprime_le_one
      (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc) hspacing
      background budget.toRadiusChain fineSmall
  have hW : ‖T.weightedAdjoint‖ ≤
      cmp99SourceGeneratedWeightedAdjointNormBound M depth :=
    norm_cmp99Eq395GeneratedWeightedAdjoint_le Omega hM depth hspacing background
      budget fineSmall
  have hG : ‖G‖ ≤ 1 / c := by
    simpa [G, c] using norm_covarianceOfIsCoerciveCLM_le
      (cmp99SourceGeneratedPhysicalPrecision (show 2 ≤ 4 by norm_num) hM
        Omega depth spacing epsilon background budget fineSmall)
      hc
      (isCoerciveCLM_cmp99SourceGeneratedPhysicalPrecision
        (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
          fineSmall hsmall)
  have hGW : ‖G.comp T.weightedAdjoint‖ ≤
      (1 / c) * cmp99SourceGeneratedWeightedAdjointNormBound M depth :=
    (ContinuousLinearMap.opNorm_comp_le G T.weightedAdjoint).trans
      (mul_le_mul hG hW (norm_nonneg T.weightedAdjoint) (by positivity))
  have hGGW : ‖G.comp (G.comp T.weightedAdjoint)‖ ≤
      (1 / c) * ((1 / c) *
        cmp99SourceGeneratedWeightedAdjointNormBound M depth) :=
    (ContinuousLinearMap.opNorm_comp_le G (G.comp T.weightedAdjoint)).trans
      (mul_le_mul hG hGW (norm_nonneg (G.comp T.weightedAdjoint))
        (by positivity))
  change ‖T.Qprime.comp (G.comp (G.comp T.weightedAdjoint))‖ ≤ _
  calc
    ‖T.Qprime.comp (G.comp (G.comp T.weightedAdjoint))‖ ≤
        ‖T.Qprime‖ * ‖G.comp (G.comp T.weightedAdjoint)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ((1 / c) * ((1 / c) *
        cmp99SourceGeneratedWeightedAdjointNormBound M depth)) := by
      exact mul_le_mul hQ hGGW (norm_nonneg _) zero_le_one
    _ = (1 / c) ^ 2 *
        cmp99SourceGeneratedWeightedAdjointNormBound M depth := by ring

/-- The literal global middle of equation (3.95), transported to the full
ambient coarse torus, satisfies the same volume-independent bound. -/
theorem norm_cmp99Eq395PhysicalGlobalMiddle_le
    (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    ‖CMP99SourceDependentOmegaGeometry.cmp99Eq395PhysicalGlobalMiddle
        hM depth hspacing background budget fineSmall hsmall‖ ≤
      (1 / cmp99SourceGeneratedCoercivity 4 M (depth + 1)
          spacing epsilon) ^ 2 *
        cmp99SourceGeneratedWeightedAdjointNormBound M depth := by
  let Omega :=
    CMP99SourceDependentOmegaGeometry.cmp99Eq395FullCoarseRegion (Q := Q)
  let Middle := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
    (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
      fineSmall hsmall
  let B := (1 / cmp99SourceGeneratedCoercivity 4 M (depth + 1)
      spacing epsilon) ^ 2 *
    cmp99SourceGeneratedWeightedAdjointNormBound M depth
  have hMiddle : ‖Middle‖ ≤ B := by
    simpa [Middle, B] using
      norm_cmp99Eq395GeneratedMiddle_le Omega hM depth hspacing background budget
        fineSmall hsmall
  have hs := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    Omega (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall
  let MiddleCoordinates := cmp99SourceTerminalCLMTransport hs hs Middle
  have hCoordinates : ‖MiddleCoordinates‖ ≤ B := by
    rw [show ‖MiddleCoordinates‖ = ‖Middle‖ by
      exact norm_cmp99SourceTerminalCLMTransport hs hs Middle]
    exact hMiddle
  have hB : 0 ≤ B := (norm_nonneg MiddleCoordinates).trans hCoordinates
  let E := extendZeroZeroCLM (𝔤 := SUNLieCoord Nc) Omega
  let R := restrictZeroCLM (𝔤 := SUNLieCoord Nc) Omega
  have hE : ‖E‖ ≤ 1 := norm_extendZeroZeroCLM_operator_le_one Omega
  have hR : ‖R‖ ≤ 1 := norm_restrictZeroCLM_operator_le_one Omega
  have hMR : ‖MiddleCoordinates.comp R‖ ≤ B := by
    calc
      ‖MiddleCoordinates.comp R‖ ≤ ‖MiddleCoordinates‖ * ‖R‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ B * 1 := mul_le_mul hCoordinates hR (norm_nonneg R) hB
      _ = B := mul_one _
  change ‖E.comp (MiddleCoordinates.comp R)‖ ≤ B
  calc
    ‖E.comp (MiddleCoordinates.comp R)‖ ≤
        ‖E‖ * ‖MiddleCoordinates.comp R‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * B := mul_le_mul hE hMR (norm_nonneg _) zero_le_one
    _ = B := one_mul _

end
end YangMills.RG
