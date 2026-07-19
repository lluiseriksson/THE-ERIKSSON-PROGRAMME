/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceRecursivePhysicalTower
import YangMills.RG.BalabanCMP99SourceCoarseCovariance

/-!
# The source-weighted CMP99 coarse covariance

CMP99 takes the adjoint of `Q'_j` in the lattice-spacing Hilbert products.
That adjoint is the explicitly constructed `weightedAdjoint`, not Lean's
counting-space `ContinuousLinearMap.adjoint`.  This file builds the printed
middle operator with that adjoint and eliminates the formerly free lower
bound on the regional adjoint.

If `A` is the regional precision, `G = A⁻¹`, and `‖A‖ ≤ Λ`, then the exact
weighted pairing and norm identities of the physical tower give

`Q' G² Q'† ≥ Λ⁻² I`.

The source normalization is `C_j = 1` in the weighted convention, so the
coercivity constant is exactly `C_j / Λ² = Λ⁻²`.  No surjectivity or lower
bound hypothesis for `Q'†` occurs in the theorem.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {d N : ℕ} {g : Type} [NeZero N]
variable [NormedAddCommGroup g] [InnerProductSpace ℝ g]
variable [FiniteDimensional ℝ g]
variable {Omega : ActiveGaugeRegion d N} {spacing : ℝ}

/-- Literal source middle operator, using the adjoint for the printed
lattice-spacing scalar products. -/
noncomputable def cmp99SourceTowerCoarseCovarianceMiddle
    (T : CMP99SourceWeightedRegionalTower (g := g) Omega spacing)
    (G : ActiveGaugeZeroCochain Omega g →L[ℝ]
      ActiveGaugeZeroCochain Omega g) :
    T.TerminalSpace.carrier →L[ℝ] T.TerminalSpace.carrier :=
  T.Qprime.comp (G.comp (G.comp T.weightedAdjoint))

/-- Exact quadratic-form identity with both source spacing weights visible.
This is the weighted analogue of `⟨eta,QG²Q*eta⟩ = ‖GQ*eta‖²`. -/
theorem weighted_inner_cmp99SourceTowerCoarseCovarianceMiddle
    (T : CMP99SourceWeightedRegionalTower (g := g) Omega spacing)
    (G : ActiveGaugeZeroCochain Omega g →L[ℝ]
      ActiveGaugeZeroCochain Omega g)
    (hG : G.IsSymmetric) (eta : T.TerminalSpace.carrier) :
    T.terminalSpacing ^ d *
        inner ℝ eta (cmp99SourceTowerCoarseCovarianceMiddle T G eta) =
      spacing ^ d * ‖G (T.weightedAdjoint eta)‖ ^ 2 := by
  have hpair := T.weightedAdjoint_pairing
    (G (G (T.weightedAdjoint eta))) eta
  change T.terminalSpacing ^ d *
      inner ℝ (T.Qprime (G (G (T.weightedAdjoint eta)))) eta =
    spacing ^ d * inner ℝ (G (G (T.weightedAdjoint eta)))
      (T.weightedAdjoint eta) at hpair
  change T.terminalSpacing ^ d *
      inner ℝ eta
        (T.Qprime (G (G (T.weightedAdjoint eta)))) =
    spacing ^ d * ‖G (T.weightedAdjoint eta)‖ ^ 2
  calc
    T.terminalSpacing ^ d *
        inner ℝ eta (T.Qprime (G (G (T.weightedAdjoint eta)))) =
      T.terminalSpacing ^ d *
        inner ℝ (T.Qprime (G (G (T.weightedAdjoint eta)))) eta := by
      rw [real_inner_comm]
    T.terminalSpacing ^ d *
        inner ℝ (T.Qprime (G (G (T.weightedAdjoint eta)))) eta =
      spacing ^ d *
        inner ℝ (G (G (T.weightedAdjoint eta)))
          (T.weightedAdjoint eta) := hpair
    _ = spacing ^ d *
        inner ℝ (T.weightedAdjoint eta)
          (G (G (T.weightedAdjoint eta))) := by
      rw [real_inner_comm]
    _ = spacing ^ d *
        inner ℝ (G (T.weightedAdjoint eta))
          (G (T.weightedAdjoint eta)) := by
      congr 1
      exact (hG (T.weightedAdjoint eta)
        (G (T.weightedAdjoint eta))).symm
    _ = spacing ^ d * ‖G (T.weightedAdjoint eta)‖ ^ 2 := by
      rw [real_inner_self_eq_norm_sq]

/-- The exact source normalization removes any independent lower-bound or
surjectivity premise for the adjoint average. -/
theorem isCoerciveCLM_cmp99SourceTowerCoarseCovarianceMiddle
    (T : CMP99SourceWeightedRegionalTower (g := g) Omega spacing)
    (A : ActiveGaugeZeroCochain Omega g →L[ℝ]
      ActiveGaugeZeroCochain Omega g)
    {c Lambda : ℝ}
    (hspacing : 0 < spacing) (hterminal : 0 < T.terminalSpacing)
    (hc : 0 < c) (hLambdaPos : 0 < Lambda)
    (hA : IsCoerciveCLM A c) (hSymm : A.IsSymmetric)
    (hLambda : ‖A‖ ≤ Lambda) :
    IsCoerciveCLM
      (cmp99SourceTowerCoarseCovarianceMiddle T
        (covarianceOfIsCoerciveCLM A hc hA)) (Lambda ^ 2)⁻¹ := by
  intro eta
  let G := covarianceOfIsCoerciveCLM A hc hA
  have hGsymm : G.IsSymmetric :=
    covarianceOfIsCoerciveCLM_isSymmetric A hc hA hSymm
  have hmiddle := weighted_inner_cmp99SourceTowerCoarseCovarianceMiddle
    T G hGsymm eta
  have hinverse := norm_le_mul_norm_covarianceOfIsCoerciveCLM
    A hc hA hLambda (T.weightedAdjoint eta)
  have hsquare :
      ‖T.weightedAdjoint eta‖ ^ 2 ≤
        Lambda ^ 2 * ‖G (T.weightedAdjoint eta)‖ ^ 2 := by
    nlinarith [norm_nonneg (T.weightedAdjoint eta),
      norm_nonneg (G (T.weightedAdjoint eta))]
  have hspacingPow : 0 < spacing ^ d := pow_pos hspacing d
  have hterminalPow : 0 < T.terminalSpacing ^ d :=
    pow_pos hterminal d
  have hscaled :
      T.terminalSpacing ^ d * ‖eta‖ ^ 2 ≤
        T.terminalSpacing ^ d *
          (inner ℝ eta
            (cmp99SourceTowerCoarseCovarianceMiddle T G eta) * Lambda ^ 2) := by
    calc
      T.terminalSpacing ^ d * ‖eta‖ ^ 2 =
          spacing ^ d * ‖T.weightedAdjoint eta‖ ^ 2 :=
        (T.weightedAdjoint_spacingNormSq eta).symm
      _ ≤ spacing ^ d *
          (Lambda ^ 2 * ‖G (T.weightedAdjoint eta)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsquare hspacingPow.le
      _ = T.terminalSpacing ^ d *
          (inner ℝ eta
            (cmp99SourceTowerCoarseCovarianceMiddle T G eta) * Lambda ^ 2) := by
        calc
          spacing ^ d * (Lambda ^ 2 * ‖G (T.weightedAdjoint eta)‖ ^ 2) =
              Lambda ^ 2 *
                (spacing ^ d * ‖G (T.weightedAdjoint eta)‖ ^ 2) := by ring
          _ = Lambda ^ 2 *
              (T.terminalSpacing ^ d * inner ℝ eta
                (cmp99SourceTowerCoarseCovarianceMiddle T G eta)) := by
            rw [← hmiddle]
          _ = T.terminalSpacing ^ d *
              (inner ℝ eta
                (cmp99SourceTowerCoarseCovarianceMiddle T G eta) *
                  Lambda ^ 2) := by ring
  have hbase : ‖eta‖ ^ 2 ≤
      inner ℝ eta
        (cmp99SourceTowerCoarseCovarianceMiddle T G eta) * Lambda ^ 2 :=
    by nlinarith [hscaled]
  change (Lambda ^ 2)⁻¹ * ‖eta‖ ^ 2 ≤
    inner ℝ eta (cmp99SourceTowerCoarseCovarianceMiddle T G eta)
  rw [inv_mul_eq_div]
  exact (div_le_iff₀ (sq_pos_of_pos hLambdaPos)).2 (by
    simpa [mul_comm] using hbase)

/-- The printed coarse covariance, generated without a free adjoint lower
bound. -/
noncomputable def cmp99SourceTowerCoarseCovariance
    (T : CMP99SourceWeightedRegionalTower (g := g) Omega spacing)
    (A : ActiveGaugeZeroCochain Omega g →L[ℝ]
      ActiveGaugeZeroCochain Omega g)
    {c Lambda : ℝ}
    (hspacing : 0 < spacing) (hterminal : 0 < T.terminalSpacing)
    (hc : 0 < c) (hLambdaPos : 0 < Lambda)
    (hA : IsCoerciveCLM A c) (hSymm : A.IsSymmetric)
    (hLambda : ‖A‖ ≤ Lambda) :
    T.TerminalSpace.carrier →L[ℝ] T.TerminalSpace.carrier :=
  covarianceOfIsCoerciveCLM
    (cmp99SourceTowerCoarseCovarianceMiddle T
      (covarianceOfIsCoerciveCLM A hc hA))
    (inv_pos.mpr (sq_pos_of_pos hLambdaPos))
    (isCoerciveCLM_cmp99SourceTowerCoarseCovarianceMiddle T A hspacing
      hterminal hc hLambdaPos hA hSymm hLambda)

/-- Exact left inverse equation for the generated source coarse covariance. -/
theorem cmp99SourceTowerCoarseCovariance_comp_middle
    (T : CMP99SourceWeightedRegionalTower (g := g) Omega spacing)
    (A : ActiveGaugeZeroCochain Omega g →L[ℝ]
      ActiveGaugeZeroCochain Omega g)
    {c Lambda : ℝ}
    (hspacing : 0 < spacing) (hterminal : 0 < T.terminalSpacing)
    (hc : 0 < c) (hLambdaPos : 0 < Lambda)
    (hA : IsCoerciveCLM A c) (hSymm : A.IsSymmetric)
    (hLambda : ‖A‖ ≤ Lambda) :
    (cmp99SourceTowerCoarseCovariance T A hspacing hterminal hc hLambdaPos
      hA hSymm hLambda).comp
        (cmp99SourceTowerCoarseCovarianceMiddle T
          (covarianceOfIsCoerciveCLM A hc hA)) =
      ContinuousLinearMap.id ℝ T.TerminalSpace.carrier := by
  exact covarianceOfIsCoerciveCLM_comp_precision _
    (inv_pos.mpr (sq_pos_of_pos hLambdaPos))
    (isCoerciveCLM_cmp99SourceTowerCoarseCovarianceMiddle T A hspacing
      hterminal hc hLambdaPos hA hSymm hLambda)

/-- Exact right inverse equation for the generated source coarse covariance. -/
theorem cmp99SourceTowerCoarseCovariance_middle_comp
    (T : CMP99SourceWeightedRegionalTower (g := g) Omega spacing)
    (A : ActiveGaugeZeroCochain Omega g →L[ℝ]
      ActiveGaugeZeroCochain Omega g)
    {c Lambda : ℝ}
    (hspacing : 0 < spacing) (hterminal : 0 < T.terminalSpacing)
    (hc : 0 < c) (hLambdaPos : 0 < Lambda)
    (hA : IsCoerciveCLM A c) (hSymm : A.IsSymmetric)
    (hLambda : ‖A‖ ≤ Lambda) :
    (cmp99SourceTowerCoarseCovarianceMiddle T
      (covarianceOfIsCoerciveCLM A hc hA)).comp
        (cmp99SourceTowerCoarseCovariance T A hspacing hterminal hc
          hLambdaPos hA hSymm hLambda) =
      ContinuousLinearMap.id ℝ T.TerminalSpace.carrier := by
  exact precision_comp_covarianceOfIsCoerciveCLM _
    (inv_pos.mpr (sq_pos_of_pos hLambdaPos))
    (isCoerciveCLM_cmp99SourceTowerCoarseCovarianceMiddle T A hspacing
      hterminal hc hLambdaPos hA hSymm hLambda)

end

end YangMills.RG
