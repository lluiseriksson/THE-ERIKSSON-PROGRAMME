/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedPoincareQprime
import YangMills.RG.BalabanCMP99SourceRetainedPhysicalPrecision

/-!
# Coercive physical precision generated from the source Poincare tower

For positive depth the generated energy coefficient is strictly positive.
Normalizing the absorbed Poincare inequality by that coefficient produces
the literal precision `D^* D + a_j Q'_j^* Q'_j`, with both its mass and
coercivity constants computed from the source recursion.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

theorem cmp99SourcePoincareEnergyCoeff_pos_succ
    (d M depth : ℕ) [NeZero d] [NeZero M]
    {spacing epsilon : ℝ} (hspacing : 0 < spacing) :
    0 < cmp99SourcePoincareEnergyCoeff d M (depth + 1) spacing epsilon := by
  simp only [cmp99SourcePoincareEnergyCoeff]
  exact mul_pos cmp99OneScaleBlockPoincareConstant_pos
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos hspacing)
      (mul_nonneg
        (mul_nonneg (by positivity)
          (cmp99SourceBlockAverageWeight_nonneg M d))
        (cmp99SourcePoincareEnergyCoeff_nonneg d M depth
          ((M : ℝ) * spacing)
          (cmp99SourceUbarNextFineRadius d M epsilon))))

/-- The printed terminal mass coefficient after normalizing the fine
derivative coefficient to one. -/
noncomputable def cmp99SourceGeneratedPhysicalMass
    (d M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  cmp99OneScaleBlockPoincareConstant d M ^ depth /
    cmp99SourcePoincareEnergyCoeff d M depth spacing epsilon

/-- The coercivity constant produced by the absorbed source Poincare
inequality. -/
noncomputable def cmp99SourceGeneratedCoercivity
    (d M depth : ℕ) (spacing epsilon : ℝ) : ℝ :=
  (1 - cmp99SourcePoincareErrorCoeff d M depth spacing epsilon) /
    cmp99SourcePoincareEnergyCoeff d M depth spacing epsilon

theorem normalized_coercivity_of_absorbed
    {fieldNorm energy mass A B C : ℝ}
    (hA : 0 < A) (hB : B < 1)
    (h : fieldNorm ≤ (A * energy + C * mass) / (1 - B)) :
    (1 - B) / A * fieldNorm ≤ energy + C / A * mass := by
  have hden : 0 < 1 - B := sub_pos.mpr hB
  have hmul : (1 - B) * fieldNorm ≤ A * energy + C * mass :=
    by simpa [mul_comm] using (le_div_iff₀ hden).mp h
  calc
    (1 - B) / A * fieldNorm = ((1 - B) * fieldNorm) / A := by ring
    _ ≤ (A * energy + C * mass) / A :=
      div_le_div_of_nonneg_right hmul hA.le
    _ = energy + C / A * mass := by
      field_simp [ne_of_gt hA]

/-- Literal source-generated regional precision at positive depth. -/
noncomputable def cmp99SourceGeneratedPhysicalPrecision
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) (spacing epsilon : ℝ)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
        (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
        (SUNLieCoord Nc) :=
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let chain := budget.toRadiusChain
  let T := regions.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
    spacing epsilon background chain fineSmall
  cmp99SourceGaugePrecision
    (cmp99ActiveRegionSourceCovariantLaplacian
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
      (matrixSUNAdjointModel Nc) background spacing)
    T.Qprime
    (cmp99SourceGeneratedPhysicalMass d M (depth + 1) spacing epsilon)

/-- B2: coercivity of the literal physical regional precision is generated
from the closed source budget and the explicit scalar absorption condition;
no `hDelta` premise remains. -/
theorem isCoerciveCLM_cmp99SourceGeneratedPhysicalPrecision
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
    IsCoerciveCLM
      (cmp99SourceGeneratedPhysicalPrecision hd hM Omega depth spacing epsilon
        background budget fineSmall)
      (cmp99SourceGeneratedCoercivity d M (depth + 1) spacing epsilon) := by
  intro phi
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let chain := budget.toRadiusChain
  let T := regions.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
    spacing epsilon background chain fineSmall
  have habs := cmp99SourceIteratedLift_norm_sq_le_absorbed_poincare_with_Qprime
    hd hM Omega (depth + 1) hspacing background budget fineSmall phi hsmall
  have hA := cmp99SourcePoincareEnergyCoeff_pos_succ d M depth hspacing
    (epsilon := epsilon)
  have hnorm := normalized_coercivity_of_absorbed hA hsmall habs
  rw [cmp99SourceGeneratedPhysicalPrecision,
    inner_cmp99SourceGaugePrecision,
    inner_cmp99ActiveRegionSourceCovariantLaplacian]
  exact hnorm

theorem cmp99SourceGeneratedCoercivity_pos
    (d M depth : ℕ) [NeZero d] [NeZero M]
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (hsmall : cmp99SourcePoincareErrorCoeff d M (depth + 1)
      spacing epsilon < 1) :
    0 < cmp99SourceGeneratedCoercivity d M (depth + 1) spacing epsilon := by
  exact div_pos (sub_pos.mpr hsmall)
    (cmp99SourcePoincareEnergyCoeff_pos_succ d M depth hspacing)

theorem cmp99SourceGeneratedPhysicalPrecision_isSymmetric
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (depth : ℕ) (spacing epsilon : ℝ)
    (background : GaugeConfig d
      (cmp99RegionalLatticeSize M N (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget d M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    (cmp99SourceGeneratedPhysicalPrecision hd hM Omega depth spacing epsilon
      background budget fineSmall).IsSymmetric := by
  unfold cmp99SourceGeneratedPhysicalPrecision
  exact cmp99SourceGaugePrecision_isSymmetric _ _ _
    (cmp99ActiveRegionSourceCovariantLaplacian_isSymmetric
      (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
      (matrixSUNAdjointModel Nc) background spacing)

/-- B3: the regional Green operator generated from the physical precision
and its internally proved coercivity. -/
noncomputable def cmp99SourceGeneratedPhysicalGreen
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
    ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
        (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega (depth + 1))
        (SUNLieCoord Nc) :=
  covarianceOfIsCoerciveCLM
    (cmp99SourceGeneratedPhysicalPrecision hd hM Omega depth spacing epsilon
      background budget fineSmall)
    (cmp99SourceGeneratedCoercivity_pos d M depth hspacing hsmall)
    (isCoerciveCLM_cmp99SourceGeneratedPhysicalPrecision hd hM Omega depth
      hspacing background budget fineSmall hsmall)

theorem cmp99SourceGeneratedPhysicalPrecision_comp_green
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
    (cmp99SourceGeneratedPhysicalPrecision hd hM Omega depth spacing epsilon
      background budget fineSmall).comp
        (cmp99SourceGeneratedPhysicalGreen hd hM Omega depth hspacing
          background budget fineSmall hsmall) =
      ContinuousLinearMap.id ℝ _ := by
  exact precision_comp_covarianceOfIsCoerciveCLM _
    (cmp99SourceGeneratedCoercivity_pos d M depth hspacing hsmall) _

theorem cmp99SourceGeneratedPhysicalGreen_comp_precision
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
    (cmp99SourceGeneratedPhysicalGreen hd hM Omega depth hspacing
      background budget fineSmall hsmall).comp
        (cmp99SourceGeneratedPhysicalPrecision hd hM Omega depth spacing epsilon
          background budget fineSmall) =
      ContinuousLinearMap.id ℝ _ := by
  exact covarianceOfIsCoerciveCLM_comp_precision _
    (cmp99SourceGeneratedCoercivity_pos d M depth hspacing hsmall) _

end

end YangMills.RG
