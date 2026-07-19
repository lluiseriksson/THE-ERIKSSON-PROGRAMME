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

/-- Relation between Lean's counting-space adjoint and the adjoint for the
printed lattice-spacing Hilbert products. -/
theorem CMP99SourceWeightedRegionalTower.adjoint_eq_spacingRatio_smul_weightedAdjoint
    (T : CMP99SourceWeightedRegionalTower (g := g) Omega spacing)
    (hterminal : T.terminalSpacing ≠ 0) :
    T.Qprime.adjoint =
      (spacing ^ d / T.terminalSpacing ^ d) • T.weightedAdjoint := by
  apply ContinuousLinearMap.ext
  intro eta
  apply ext_inner_right ℝ
  intro phi
  rw [ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.smul_apply, inner_smul_left]
  rw [starRingEnd_apply, star_trivial]
  have hpair := T.weightedAdjoint_pairing phi eta
  change T.terminalSpacing ^ d * inner ℝ (T.Qprime phi) eta =
    spacing ^ d * inner ℝ phi (T.weightedAdjoint eta) at hpair
  have hpow : T.terminalSpacing ^ d ≠ 0 := pow_ne_zero d hterminal
  calc
    inner ℝ eta (T.Qprime phi) = inner ℝ (T.Qprime phi) eta :=
      real_inner_comm _ _
    _ = (spacing ^ d / T.terminalSpacing ^ d) *
        inner ℝ phi (T.weightedAdjoint eta) := by
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff hpow).2
      simpa [mul_comm, mul_left_comm, mul_assoc] using hpair
    _ = (spacing ^ d / T.terminalSpacing ^ d) *
        inner ℝ (T.weightedAdjoint eta) phi := by
      rw [real_inner_comm]

/-- Counting-space coisometry constant corresponding to the source-weighted
normalization `C_j = 1`. -/
theorem CMP99SourceWeightedRegionalTower.Qprime_comp_adjoint_eq_spacingRatio
    (T : CMP99SourceWeightedRegionalTower (g := g) Omega spacing)
    (hterminal : T.terminalSpacing ≠ 0) :
    T.Qprime.comp T.Qprime.adjoint =
      (spacing ^ d / T.terminalSpacing ^ d) •
        ContinuousLinearMap.id ℝ T.TerminalSpace.carrier := by
  rw [T.adjoint_eq_spacingRatio_smul_weightedAdjoint hterminal]
  apply ContinuousLinearMap.ext
  intro eta
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul,
    ContinuousLinearMap.id_apply]
  have h := congrArg
    (fun A : T.TerminalSpace.carrier →L[ℝ] T.TerminalSpace.carrier => A eta)
    T.Qprime_comp_weightedAdjoint
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    using congrArg
      (fun x : T.TerminalSpace.carrier =>
        (spacing ^ d / T.terminalSpacing ^ d) • x) h

/-- Exact counting-space operator norm of the recursive average. -/
theorem CMP99SourceWeightedRegionalTower.norm_Qprime_sq_eq_spacingRatio
    (T : CMP99SourceWeightedRegionalTower (g := g) Omega spacing)
    [Nontrivial T.TerminalSpace.carrier]
    (hspacing : 0 ≤ spacing) (hterminal : 0 < T.terminalSpacing) :
    ‖T.Qprime‖ ^ 2 = spacing ^ d / T.terminalSpacing ^ d := by
  have hcomp := T.Qprime_comp_adjoint_eq_spacingRatio hterminal.ne'
  have hnorm := ContinuousLinearMap.norm_adjoint_comp_self T.Qprime.adjoint
  rw [ContinuousLinearMap.adjoint_adjoint] at hnorm
  rw [hcomp] at hnorm
  have hratio : 0 ≤ spacing ^ d / T.terminalSpacing ^ d :=
    div_nonneg (pow_nonneg hspacing d) (pow_pos hterminal d).le
  rw [norm_smul, ContinuousLinearMap.norm_id, mul_one,
    Real.norm_eq_abs, abs_of_nonneg hratio] at hnorm
  simpa only [LinearIsometryEquiv.norm_map, pow_two] using hnorm.symm

/-- A source tower is a contraction in counting norm whenever its terminal
spacing is no smaller than its fine spacing. -/
theorem CMP99SourceWeightedRegionalTower.norm_Qprime_le_one
    (T : CMP99SourceWeightedRegionalTower (g := g) Omega spacing)
    [Nontrivial T.TerminalSpace.carrier]
    (hspacing : 0 ≤ spacing)
    (hterminal : 0 < T.terminalSpacing)
    (hmono : spacing ≤ T.terminalSpacing) :
    ‖T.Qprime‖ ≤ 1 := by
  have hsq := T.norm_Qprime_sq_eq_spacingRatio hspacing hterminal
  have hpow := pow_le_pow_left₀ hspacing hmono d
  have hratio : spacing ^ d / T.terminalSpacing ^ d ≤ 1 := by
    apply (div_le_iff₀ (pow_pos hterminal d)).2
    simpa using hpow
  nlinarith [norm_nonneg T.Qprime]

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
