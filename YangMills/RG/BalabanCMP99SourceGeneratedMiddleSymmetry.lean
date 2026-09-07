/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedPhysicalCoarseCovariance

/-!
# Symmetry of the generated CMP99 middle operator

The global--regional defect enters equation (3.95) in the adjoint
orientation.  This file proves from the weighted source pairing that the
literal middle `Q' G^2 Q'^*` is symmetric.  The proof retains both lattice
spacing weights and introduces no normalization or finite-volume constant.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- A source tower middle is symmetric whenever its Green operator is
symmetric and the terminal spacing is positive. -/
theorem cmp99SourceTowerCoarseCovarianceMiddle_isSymmetric
    {Omega : ActiveGaugeRegion d N} {spacing : ℝ}
    (T : CMP99SourceWeightedRegionalTower
      (g := SUNLieCoord Nc) Omega spacing)
    (G : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    (hterminal : 0 < T.terminalSpacing) (hG : G.IsSymmetric) :
    (cmp99SourceTowerCoarseCovarianceMiddle T G).IsSymmetric := by
  intro x y
  let Middle := cmp99SourceTowerCoarseCovarianceMiddle T G
  have hx := T.weightedAdjoint_pairing
    (G (G (T.weightedAdjoint x))) y
  have hy := T.weightedAdjoint_pairing
    (G (G (T.weightedAdjoint y))) x
  change T.terminalSpacing ^ d * inner ℝ (Middle x) y =
    spacing ^ d * inner ℝ (G (G (T.weightedAdjoint x)))
      (T.weightedAdjoint y) at hx
  change T.terminalSpacing ^ d * inner ℝ (Middle y) x =
    spacing ^ d * inner ℝ (G (G (T.weightedAdjoint y)))
      (T.weightedAdjoint x) at hy
  have hxy :
      inner ℝ (G (G (T.weightedAdjoint x))) (T.weightedAdjoint y) =
        inner ℝ (G (T.weightedAdjoint x))
          (G (T.weightedAdjoint y)) :=
    hG (G (T.weightedAdjoint x)) (T.weightedAdjoint y)
  have hyx :
      inner ℝ (G (G (T.weightedAdjoint y))) (T.weightedAdjoint x) =
        inner ℝ (G (T.weightedAdjoint y))
          (G (T.weightedAdjoint x)) :=
    hG (G (T.weightedAdjoint y)) (T.weightedAdjoint x)
  rw [hxy] at hx
  rw [hyx] at hy
  have hy' : T.terminalSpacing ^ d * inner ℝ x (Middle y) =
      spacing ^ d * inner ℝ (G (T.weightedAdjoint x))
        (G (T.weightedAdjoint y)) := by
    calc
      T.terminalSpacing ^ d * inner ℝ x (Middle y) =
          T.terminalSpacing ^ d * inner ℝ (Middle y) x := by
        rw [real_inner_comm]
      _ = spacing ^ d * inner ℝ (G (T.weightedAdjoint y))
          (G (T.weightedAdjoint x)) := hy
      _ = spacing ^ d * inner ℝ (G (T.weightedAdjoint x))
          (G (T.weightedAdjoint y)) := by
        rw [real_inner_comm]
  have hpow : 0 < T.terminalSpacing ^ d := pow_pos hterminal d
  exact mul_left_cancel₀ hpow.ne' (hx.trans hy'.symm)

/-- The generated physical regional Green is symmetric. -/
theorem cmp99SourceGeneratedPhysicalGreen_isSymmetric
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
    (cmp99SourceGeneratedPhysicalGreen hd hM Omega depth hspacing background
      budget fineSmall hsmall).IsSymmetric := by
  exact covarianceOfIsCoerciveCLM_isSymmetric
    (cmp99SourceGeneratedPhysicalPrecision hd hM Omega depth spacing epsilon
      background budget fineSmall)
    (cmp99SourceGeneratedCoercivity_pos d M depth hspacing hsmall)
    (isCoerciveCLM_cmp99SourceGeneratedPhysicalPrecision hd hM Omega depth
      hspacing background budget fineSmall hsmall)
    (cmp99SourceGeneratedPhysicalPrecision_isSymmetric hd hM Omega depth
      spacing epsilon background budget fineSmall)

/-- The generated physical middle is symmetric on every literal source
region. -/
theorem cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle_isSymmetric
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
      hspacing background budget fineSmall hsmall).IsSymmetric := by
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let T := regions.weightedQprimeTower hd hM (matrixSUNAdjointModel Nc)
    spacing epsilon background budget.toRadiusChain fineSmall
  let G := cmp99SourceGeneratedPhysicalGreen hd hM Omega depth hspacing
    background budget fineSmall hsmall
  have hterminalEq : T.terminalSpacing =
      (M : ℝ) ^ (depth + 1) * spacing :=
    regions.weightedQprimeTower_terminalSpacing hd hM
      (matrixSUNAdjointModel Nc) spacing epsilon background
      budget.toRadiusChain fineSmall
  have hMpos : (0 : ℝ) < M := by
    exact_mod_cast (show 0 < M by omega)
  have hterminal : 0 < T.terminalSpacing := by
    rw [hterminalEq]
    exact mul_pos (pow_pos hMpos _) hspacing
  have hG : G.IsSymmetric :=
    cmp99SourceGeneratedPhysicalGreen_isSymmetric hd hM Omega depth hspacing
      background budget fineSmall hsmall
  unfold cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
  exact cmp99SourceTowerCoarseCovarianceMiddle_isSymmetric T G hterminal hG

/-- Adjoint form of generated middle symmetry. -/
theorem cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle_adjoint_eq
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
      hspacing background budget fineSmall hsmall).adjoint =
      cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle hd hM Omega depth
        hspacing background budget fineSmall hsmall :=
  (cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle_isSymmetric hd hM Omega
    depth hspacing background budget fineSmall hsmall).clm_adjoint_eq

end
end YangMills.RG
