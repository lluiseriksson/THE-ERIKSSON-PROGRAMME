/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395GlobalMiddleNorm

/-!
# Uniform norms of the localized atoms in CMP99 equation (3.95)

The second and third atoms in the exhaustive physical family are supported on
one source cell.  This file supplies their volume-independent operator norms.
It first transports the generated middle and covariance through restriction
and zero extension, then combines the exact atom factorizations with the
contractive characteristic and smooth multipliers.  No spatial claim is made
for the first atom: its global middle requires a genuine weighted-kernel
estimate rather than an ambient operator-norm bound.
-/

namespace YangMills.RG
open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace
noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

/-- Restriction and zero extension do not increase a regional operator bound. -/
theorem norm_cmp99Eq395_extend_comp_comp_restrict_le
    {d N : ℕ} [NeZero N] {g : Type*}
    [NormedAddCommGroup g] [InnerProductSpace ℝ g] [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N)
    (F : ActiveGaugeZeroCochain Omega g →L[ℝ]
      ActiveGaugeZeroCochain Omega g)
    {A : ℝ} (hF : ‖F‖ ≤ A) :
    ‖(extendZeroZeroCLM Omega).comp (F.comp (restrictZeroCLM Omega))‖ ≤ A := by
  have hA : 0 ≤ A := (norm_nonneg F).trans hF
  have hE := norm_extendZeroZeroCLM_operator_le_one (g := g) Omega
  have hR := norm_restrictZeroCLM_operator_le_one (g := g) Omega
  have hFR : ‖F.comp (restrictZeroCLM Omega)‖ ≤ A := by
    calc
      ‖F.comp (restrictZeroCLM Omega)‖ ≤
          ‖F‖ * ‖restrictZeroCLM (𝔤 := g) Omega‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ A * 1 := mul_le_mul hF hR
        (norm_nonneg (restrictZeroCLM (𝔤 := g) Omega)) hA
      _ = A := mul_one _
  calc
    ‖(extendZeroZeroCLM Omega).comp (F.comp (restrictZeroCLM Omega))‖ ≤
        ‖extendZeroZeroCLM (𝔤 := g) Omega‖ *
          ‖F.comp (restrictZeroCLM Omega)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * A := mul_le_mul hE hFR
      (norm_nonneg (F.comp (restrictZeroCLM (𝔤 := g) Omega))) zero_le_one
    _ = A := one_mul _

universe v
variable {M Nc Q j : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

/-- Common volume-independent bound for global and regional middles. -/
noncomputable def cmp99Eq395MiddleNormBound
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  (1 / cmp99SourceGeneratedCoercivity 4 M (depth + 1)
      spacing epsilon) ^ 2 *
    cmp99SourceGeneratedWeightedAdjointNormBound M depth

/-- Common volume-independent bound for the second and third physical atoms. -/
noncomputable def cmp99Eq395LocalizedAtomNormBound
    (M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  2 * cmp99Eq395MiddleNormBound M depth spacing epsilon *
    cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound
      M depth spacing epsilon

namespace CMP99SourceDependentOmegaGeometry

/-- The physical smooth multiplier is contractive. -/
theorem norm_cmp99Eq395PhysicalSmoothMultiplier_le_one
    (P : CMP95SourceSmoothPartitionProfile) (cell : FinBox 4 Q) :
    ‖cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell‖ ≤ 1 := by
  exact norm_finitePiLpScalarMultiplier_le_one _
    (fun block =>
      (cmp95SourcePeriodicCoarseSquarePartition P Q).norm_value_le_one
        cell block)

/-- The physical source-cell characteristic is contractive. -/
theorem norm_cmp99Eq395PhysicalSourceCharacteristic_le_one (cell : FinBox 4 Q) :
    ‖cmp99Eq395PhysicalSourceCharacteristic (Nc := Nc) cell‖ ≤ 1 := by
  exact norm_finitePiLpScalarMultiplier_le_one _
    (fun block => norm_cmp99SourcePiCharacteristic_le_one cell block)

/-- Uniform norm of the regional middle after ambient transport. -/
theorem norm_cmp99Eq395PhysicalMiddle_le
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (cell : FinBox 4 Q) :
    ‖cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background budget
      fineSmall hsmall cell‖ ≤
      (1 / cmp99SourceGeneratedCoercivity 4 M (depth + 1)
          spacing epsilon) ^ 2 *
        cmp99SourceGeneratedWeightedAdjointNormBound M depth := by
  let Omega := (D cell).operatorCoarseRegion (hpi5 cell)
    (cmp99OmegaPi4Index j)
  let Raw := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
    (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
      fineSmall hsmall
  let B := (1 / cmp99SourceGeneratedCoercivity 4 M (depth + 1)
      spacing epsilon) ^ 2 *
    cmp99SourceGeneratedWeightedAdjointNormBound M depth
  have hRaw : ‖Raw‖ ≤ B := by
    simpa [Raw, B] using
      norm_cmp99Eq395GeneratedMiddle_le Omega hM depth hspacing background
        budget fineSmall hsmall
  have hs := cmp99SourceIteratedLift_weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    Omega (depth + 1) spacing epsilon background budget.toRadiusChain fineSmall
  let F := cmp99SourceTerminalCLMTransport hs hs Raw
  have hF : ‖F‖ ≤ B := by
    rw [show ‖F‖ = ‖Raw‖ by
      exact norm_cmp99SourceTerminalCLMTransport hs hs Raw]
    exact hRaw
  change ‖(extendZeroZeroCLM Omega).comp
      (F.comp (restrictZeroCLM Omega))‖ ≤ B
  exact norm_cmp99Eq395_extend_comp_comp_restrict_le Omega F hF

/-- Uniform norm of the regional covariance after ambient transport. -/
theorem norm_cmp99Eq395PhysicalCovariance_le
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (cell : FinBox 4 Q) :
    ‖cmp99Eq395PhysicalCovariance D hpi5 hM depth hspacing background budget
      fineSmall hsmall cell‖ ≤
      cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound
        M depth spacing epsilon := by
  let Omega := (D cell).operatorCoarseRegion (hpi5 cell)
    (cmp99OmegaPi4Index j)
  let F := (D cell).generatedPhysicalCoarseCovarianceCoordinates
    (hpi5 cell) (cmp99OmegaPi4Index j) hM depth hspacing background budget
      fineSmall hsmall
  have hF : ‖F‖ ≤ cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound
      M depth spacing epsilon := by
    exact (D cell).norm_generatedPhysicalCoarseCovarianceCoordinates_le
      (hpi5 cell) (cmp99OmegaPi4Index j) hM depth hspacing background budget
        fineSmall hsmall
  change ‖(extendZeroZeroCLM Omega).comp
      (F.comp (restrictZeroCLM Omega))‖ ≤ _
  exact norm_cmp99Eq395_extend_comp_comp_restrict_le Omega F hF

/-- The second source-relevant atom has a volume-independent norm. -/
theorem norm_cmp99Eq395PhysicalRAtom_second_le
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (cell : FinBox 4 Q) :
    ‖cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing background budget
      fineSmall hsmall (cell, .second)‖ ≤
      cmp99Eq395LocalizedAtomNormBound M depth spacing epsilon := by
  let A := cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background budget
    fineSmall hsmall
  let AD := cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
    budget fineSmall hsmall cell
  let chi := cmp99Eq395PhysicalSourceCharacteristic (Nc := Nc) cell
  let Head := cmp99Eq395PhysicalHead D hpi5 P hM depth hspacing background
    budget fineSmall hsmall cell
  let B := cmp99Eq395MiddleNormBound M depth spacing epsilon
  let C := cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound
    M depth spacing epsilon
  have hA : ‖A‖ ≤ B := by
    simpa [A, B, cmp99Eq395MiddleNormBound] using
      norm_cmp99Eq395PhysicalGlobalMiddle_le hM depth hspacing background
        budget fineSmall hsmall
  have hAD : ‖AD‖ ≤ B := by
    simpa [AD, B, cmp99Eq395MiddleNormBound] using
      norm_cmp99Eq395PhysicalMiddle_le D hpi5 hM depth hspacing background budget
        fineSmall hsmall cell
  have hchi : ‖chi‖ ≤ 1 := by
    simpa [chi] using norm_cmp99Eq395PhysicalSourceCharacteristic_le_one
      (Nc := Nc) cell
  have hHead : ‖Head‖ ≤ C := by
    simpa [Head, C] using norm_cmp99Eq395PhysicalHead_le D hpi5 P hM depth
      hspacing background budget fineSmall hsmall cell
  have hB : 0 ≤ B := (norm_nonneg A).trans hA
  have hC : 0 ≤ C := (norm_nonneg Head).trans hHead
  have hdiff : ‖A - AD‖ ≤ 2 * B := by
    calc
      ‖A - AD‖ ≤ ‖A‖ + ‖AD‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add hA hAD
      _ = 2 * B := by ring
  have hleftSecond : ‖chi * (A - AD)‖ ≤ 2 * B := by
    calc
      ‖chi * (A - AD)‖ ≤ ‖chi‖ * ‖A - AD‖ := norm_mul_le _ _
      _ ≤ 1 * (2 * B) :=
        mul_le_mul hchi hdiff (norm_nonneg (A - AD)) zero_le_one
      _ = 2 * B := one_mul _
  rw [cmp99Eq395PhysicalRAtom_second_eq]
  rw [norm_neg]
  calc
    ‖cmp99Eq395PhysicalSecondLeft D hpi5 hM depth hspacing background
        budget fineSmall hsmall cell * Head‖ ≤
      ‖cmp99Eq395PhysicalSecondLeft D hpi5 hM depth hspacing background
        budget fineSmall hsmall cell‖ * ‖Head‖ := norm_mul_le _ _
    _ ≤ (2 * B) * C := by
      apply mul_le_mul _ hHead (norm_nonneg Head) (mul_nonneg (by norm_num) hB)
      change ‖chi * (A - AD)‖ ≤ 2 * B
      exact hleftSecond
    _ = cmp99Eq395LocalizedAtomNormBound M depth spacing epsilon := by
      rfl

/-- The third source-relevant atom has the same volume-independent norm. -/
theorem norm_cmp99Eq395PhysicalRAtom_third_le
    (D : (cell : FinBox 4 Q) → CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : ∀ cell, (D cell).fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (P : CMP95SourceSmoothPartitionProfile)
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1)
    (cell : FinBox 4 Q) :
    ‖cmp99Eq395PhysicalRAtom D hpi5 P hM depth hspacing background budget
      fineSmall hsmall (cell, .third)‖ ≤
      cmp99Eq395LocalizedAtomNormBound M depth spacing epsilon := by
  let AD := cmp99Eq395PhysicalMiddle D hpi5 hM depth hspacing background
    budget fineSmall hsmall cell
  let chi := cmp99Eq395PhysicalSourceCharacteristic (Nc := Nc) cell
  let h := cmp99Eq395PhysicalSmoothMultiplier (Nc := Nc) P cell
  let COp := cmp99Eq395PhysicalCovariance D hpi5 hM depth hspacing background
    budget fineSmall hsmall cell
  let B := cmp99Eq395MiddleNormBound M depth spacing epsilon
  let C := cmp99SourceGeneratedPhysicalCoarseCovarianceNormBound
    M depth spacing epsilon
  have hAD : ‖AD‖ ≤ B := by
    simpa [AD, B, cmp99Eq395MiddleNormBound] using
      norm_cmp99Eq395PhysicalMiddle_le D hpi5 hM depth hspacing background budget
        fineSmall hsmall cell
  have hchi : ‖chi‖ ≤ 1 := by
    simpa [chi] using norm_cmp99Eq395PhysicalSourceCharacteristic_le_one
      (Nc := Nc) cell
  have hh : ‖h‖ ≤ 1 := by
    simpa [h] using norm_cmp99Eq395PhysicalSmoothMultiplier_le_one
      (Nc := Nc) P cell
  have hCOp : ‖COp‖ ≤ C := by
    simpa [COp, C] using norm_cmp99Eq395PhysicalCovariance_le D hpi5 hM depth
      hspacing background budget fineSmall hsmall cell
  have hB : 0 ≤ B := (norm_nonneg AD).trans hAD
  have hC : 0 ≤ C := (norm_nonneg COp).trans hCOp
  have hchiAD : ‖chi * AD‖ ≤ B := by
    calc
      ‖chi * AD‖ ≤ ‖chi‖ * ‖AD‖ := norm_mul_le _ _
      _ ≤ 1 * B := mul_le_mul hchi hAD (norm_nonneg AD) zero_le_one
      _ = B := one_mul _
  have hchiADh : ‖chi * AD * h‖ ≤ B := by
    calc
      ‖chi * AD * h‖ ≤ ‖chi * AD‖ * ‖h‖ := norm_mul_le _ _
      _ ≤ B * 1 := mul_le_mul hchiAD hh (norm_nonneg h) hB
      _ = B := mul_one _
  have hhchiAD : ‖h * (chi * AD)‖ ≤ B := by
    calc
      ‖h * (chi * AD)‖ ≤ ‖h‖ * ‖chi * AD‖ := norm_mul_le _ _
      _ ≤ 1 * B := mul_le_mul hh hchiAD (norm_nonneg (chi * AD)) zero_le_one
      _ = B := one_mul _
  have hleft : ‖chi * AD * h - h * (chi * AD)‖ ≤ 2 * B := by
    calc
      ‖chi * AD * h - h * (chi * AD)‖ ≤
          ‖chi * AD * h‖ + ‖h * (chi * AD)‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add hchiADh hhchiAD
      _ = 2 * B := by ring
  have htail : ‖COp * h‖ ≤ C := by
    calc
      ‖COp * h‖ ≤ ‖COp‖ * ‖h‖ := norm_mul_le _ _
      _ ≤ C * 1 := mul_le_mul hCOp hh (norm_nonneg h) hC
      _ = C := mul_one _
  rw [cmp99Eq395PhysicalRAtom_third_eq]
  rw [norm_neg]
  calc
    ‖cmp99Eq395PhysicalThirdLeft D hpi5 P hM depth hspacing background
        budget fineSmall hsmall cell *
      cmp99Eq395PhysicalRightTail D hpi5 P hM depth hspacing background
        budget fineSmall hsmall cell‖ ≤
      ‖cmp99Eq395PhysicalThirdLeft D hpi5 P hM depth hspacing background
        budget fineSmall hsmall cell‖ *
      ‖cmp99Eq395PhysicalRightTail D hpi5 P hM depth hspacing background
        budget fineSmall hsmall cell‖ := norm_mul_le _ _
    _ ≤ (2 * B) * C := by
      apply mul_le_mul _ _ (norm_nonneg _) (mul_nonneg (by norm_num) hB)
      · simpa [cmp99Eq395PhysicalThirdLeft, AD, chi, h] using hleft
      · simpa [cmp99Eq395PhysicalRightTail, COp, h] using htail
    _ = cmp99Eq395LocalizedAtomNormBound M depth spacing epsilon := by
      rfl

end CMP99SourceDependentOmegaGeometry
end
end YangMills.RG
