/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedPhysicalPrecision

/-!
# Generated physical coarse covariance for CMP99

The source-generated regional precision now has both an internally proved
coercivity constant and an explicit volume-independent upper bound.  This
file consumes those results together with the exact weighted coisometry of
`Q'_j` to construct

`Q'_j (G'_j)^2 (Q'_j)^dagger`

and its inverse.  Its coercivity constant is the printed `Lambda^{-2}`; no
surjectivity, adjoint lower bound, or ambient-volume hypothesis is exposed.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- The literal generated middle operator `Q'_j (G'_j)^2 (Q'_j)^dagger`. -/
noncomputable def cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
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
    T.TerminalSpace.carrier →L[ℝ] T.TerminalSpace.carrier := by
  dsimp only
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let T := regions.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
    spacing epsilon background budget.toRadiusChain fineSmall
  exact cmp99SourceTowerCoarseCovarianceMiddle T
    (cmp99SourceGeneratedPhysicalGreen hd hM Omega depth hspacing
      background budget fineSmall hsmall)

/-- The generated middle operator is coercive with the exact source
constant `Lambda^{-2}`. -/
theorem isCoerciveCLM_cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
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
      (cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle hd hM Omega depth
        hspacing background budget fineSmall hsmall)
      ((cmp99SourceGeneratedPhysicalPrecisionUpperBound d M (depth + 1)
        spacing epsilon) ^ 2)⁻¹ := by
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let T := regions.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
    spacing epsilon background budget.toRadiusChain fineSmall
  let A := cmp99SourceGeneratedPhysicalPrecision hd hM Omega depth
    spacing epsilon background budget fineSmall
  let c := cmp99SourceGeneratedCoercivity d M (depth + 1) spacing epsilon
  let Lambda := cmp99SourceGeneratedPhysicalPrecisionUpperBound
    d M (depth + 1) spacing epsilon
  have hterminalEq : T.terminalSpacing =
      (M : ℝ) ^ (depth + 1) * spacing :=
    regions.weightedQprimeTower_terminalSpacing hd hM
      (matrixSUNAdjointModel Nc) spacing epsilon background
      budget.toRadiusChain fineSmall
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hterminal : 0 < T.terminalSpacing := by
    rw [hterminalEq]
    exact mul_pos (pow_pos hMpos (depth + 1)) hspacing
  have hc : 0 < c :=
    cmp99SourceGeneratedCoercivity_pos d M depth hspacing hsmall
  have hLambdaPos : 0 < Lambda :=
    cmp99SourceGeneratedPhysicalPrecisionUpperBound_pos d M (depth + 1)
      hspacing
  have hA : IsCoerciveCLM A c :=
    isCoerciveCLM_cmp99SourceGeneratedPhysicalPrecision hd hM Omega depth
      hspacing background budget fineSmall hsmall
  have hSymm : A.IsSymmetric :=
    cmp99SourceGeneratedPhysicalPrecision_isSymmetric hd hM Omega depth
      spacing epsilon background budget fineSmall
  have hLambda : ‖A‖ ≤ Lambda :=
    norm_cmp99SourceGeneratedPhysicalPrecision_le hd hM Omega depth hspacing
      background budget fineSmall
  unfold cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
  exact isCoerciveCLM_cmp99SourceTowerCoarseCovarianceMiddle T A hspacing
    hterminal hc hLambdaPos hA hSymm hLambda

/-- The inverse coarse covariance generated from the literal source tower. -/
noncomputable def cmp99SourceGeneratedPhysicalCoarseCovariance
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
    T.TerminalSpace.carrier →L[ℝ] T.TerminalSpace.carrier :=
  covarianceOfIsCoerciveCLM
    (cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle hd hM Omega depth
      hspacing background budget fineSmall hsmall)
    (inv_pos.mpr (sq_pos_of_pos
      (cmp99SourceGeneratedPhysicalPrecisionUpperBound_pos d M (depth + 1)
        hspacing)))
    (isCoerciveCLM_cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle hd hM
      Omega depth hspacing background budget fineSmall hsmall)

theorem cmp99SourceGeneratedPhysicalCoarseCovariance_comp_middle
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
    (cmp99SourceGeneratedPhysicalCoarseCovariance hd hM Omega depth hspacing
      background budget fineSmall hsmall).comp
        (cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle hd hM Omega depth
          hspacing background budget fineSmall hsmall) =
      ContinuousLinearMap.id ℝ _ := by
  exact covarianceOfIsCoerciveCLM_comp_precision _
    (inv_pos.mpr (sq_pos_of_pos
      (cmp99SourceGeneratedPhysicalPrecisionUpperBound_pos d M (depth + 1)
        hspacing))) _

theorem cmp99SourceGeneratedPhysicalCoarseCovariance_middle_comp
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
    (cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle hd hM Omega depth
      hspacing background budget fineSmall hsmall).comp
        (cmp99SourceGeneratedPhysicalCoarseCovariance hd hM Omega depth
          hspacing background budget fineSmall hsmall) =
      ContinuousLinearMap.id ℝ _ := by
  exact precision_comp_covarianceOfIsCoerciveCLM _
    (inv_pos.mpr (sq_pos_of_pos
      (cmp99SourceGeneratedPhysicalPrecisionUpperBound_pos d M (depth + 1)
        hspacing))) _

end

end YangMills.RG
