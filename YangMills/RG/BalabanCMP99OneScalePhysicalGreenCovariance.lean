/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99OneScalePhysicalCoercivity
import YangMills.RG.BalabanCMP99SourceTowerCoarseCovariance

/-!
# One-scale physical Green and coarse covariance for CMP99

This file consumes the source-specific one-scale coercivity theorem.  It
constructs the exact Green operator and the weighted middle operator
`Q' G'^2 Q'^dagger`, proves the latter coercive with the internally generated
precision upper bound, and constructs its inverse.  Empty/trivial regional
field spaces are handled without a spurious `Nontrivial` assumption.
-/

namespace YangMills.RG

open YangMills
open scoped RealInnerProductSpace

noncomputable section

variable {Q M j Nc : ℕ} [NeZero Q] [NeZero M] [NeZero Nc]
variable {cell : FinBox 4 Q}

/-- A source tower is a counting-norm contraction even when its terminal
space is trivial. -/
theorem CMP99SourceWeightedRegionalTower.norm_Qprime_le_one_unconditional
    {d N : ℕ} {g : Type} [NeZero N]
    [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    {Omega : ActiveGaugeRegion d N} {spacing : ℝ}
    (T : CMP99SourceWeightedRegionalTower (g := g) Omega spacing)
    (hspacing : 0 ≤ spacing) (hterminal : 0 < T.terminalSpacing)
    (hmono : spacing ≤ T.terminalSpacing) :
    ‖T.Qprime‖ ≤ 1 := by
  by_cases hnontrivial : Nontrivial T.TerminalSpace.carrier
  · letI := hnontrivial
    exact T.norm_Qprime_le_one hspacing hterminal hmono
  · haveI : Subsingleton T.TerminalSpace.carrier :=
      not_nontrivial_iff_subsingleton.mp hnontrivial
    have hzero : T.Qprime = 0 := Subsingleton.elim _ _
    calc
      ‖T.Qprime‖ = 0 := by
        rw [hzero]
        exact ContinuousLinearMap.opNorm_zero
      _ ≤ 1 := zero_le_one

/-- The literal one-step physical source tower. -/
noncomputable def cmp99OmegaSourcePhysicalOneStepTower
    (Seq : CMP99SourceOmegaGeometry cell j)
    (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing : ℝ) :
    CMP99SourceWeightedRegionalTower
      (g := SUNLieCoord Nc)
      (cmp99OmegaActiveGaugeRegion (M := M) Seq r) spacing :=
  CMP99SourceWeightedRegionalTower.step
    (cmp99OmegaActiveGaugeRegion (M := M) Seq r)
    (cmp99OmegaActiveGaugeRegion_blockSaturated (M := M) Seq r)
    spacing (cmp99SourceWeightedPhysicalTransport rho U)
    (CMP99SourceWeightedRegionalTower.stop
      (g := SUNLieCoord Nc)
      (cmp99ActiveCoarseRegion
        (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq r))
      ((M : ℝ) * spacing))

@[simp] theorem cmp99OmegaSourcePhysicalOneStepTower_terminalSpacing
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing : ℝ) :
    (cmp99OmegaSourcePhysicalOneStepTower Seq r rho U spacing).terminalSpacing =
      (M : ℝ) * spacing := rfl

theorem cmp99OmegaSourcePhysicalOneStepTower_Qprime
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing : ℝ) :
    (cmp99OmegaSourcePhysicalOneStepTower Seq r rho U spacing).Qprime =
      cmp99OmegaSourcePhysicalOneStepQ Seq r rho U := by
  apply ContinuousLinearMap.ext
  intro phi
  rfl

theorem cmp99OmegaSourcePhysicalGaugePrecision_oneStepTower_eq
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing a : ℝ) :
    cmp99OmegaSourcePhysicalGaugePrecision Seq r
        (cmp99OmegaSourcePhysicalOneStepTower Seq r rho U spacing)
        rho U a =
      cmp99OmegaSourcePhysicalOneStepGaugePrecision
        Seq r rho U spacing a := by
  unfold cmp99OmegaSourcePhysicalGaugePrecision
  unfold cmp99OmegaSourcePhysicalOneStepGaugePrecision
  rw [cmp99OmegaSourcePhysicalOneStepTower_Qprime]
  rfl

/-- The explicit upper-bound constant for the one-step physical precision. -/
noncomputable def cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound
    (spacing a : ℝ) : ℝ :=
  16 / spacing ^ 2 + |a|

theorem cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound_pos
    {spacing a : ℝ} (hspacing : 0 < spacing) :
    0 < cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound spacing a := by
  unfold cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound
  have : 0 < 16 / spacing ^ 2 := by positivity
  positivity

/-- Uniform precision upper bound without a nontriviality side condition. -/
theorem norm_cmp99OmegaSourcePhysicalOneStepGaugePrecision_le
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) :
    ‖cmp99OmegaSourcePhysicalOneStepGaugePrecision
        Seq r rho U spacing a‖ ≤
      cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound spacing a := by
  let T := cmp99OmegaSourcePhysicalOneStepTower Seq r rho U spacing
  have hM : (1 : ℝ) ≤ M := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)
  have hterminal : 0 < T.terminalSpacing := by
    dsimp [T]
    positivity
  have hmono : spacing ≤ T.terminalSpacing := by
    dsimp [T]
    nlinarith
  have hQ : ‖cmp99OmegaSourcePhysicalOneStepQ Seq r rho U‖ ≤ 1 := by
    rw [← cmp99OmegaSourcePhysicalOneStepTower_Qprime
      Seq r rho U spacing]
    exact T.norm_Qprime_le_one_unconditional hspacing.le hterminal hmono
  have hDelta := norm_cmp99OmegaSourceCovariantLaplacian_le
    Seq r rho U hspacing
  rw [cmp99OmegaSourcePhysicalOneStepGaugePrecision,
    cmp99SourceGaugePrecision]
  calc
    ‖cmp99OmegaSourceCovariantLaplacian Seq r rho U spacing +
        a • ((cmp99OmegaSourcePhysicalOneStepQ Seq r rho U).adjoint.comp
          (cmp99OmegaSourcePhysicalOneStepQ Seq r rho U))‖ ≤
      ‖cmp99OmegaSourceCovariantLaplacian Seq r rho U spacing‖ +
        ‖a • ((cmp99OmegaSourcePhysicalOneStepQ Seq r rho U).adjoint.comp
          (cmp99OmegaSourcePhysicalOneStepQ Seq r rho U))‖ := norm_add_le _ _
    _ ≤ 16 / spacing ^ 2 + |a| *
        ‖cmp99OmegaSourcePhysicalOneStepQ Seq r rho U‖ ^ 2 := by
      rw [norm_smul, ContinuousLinearMap.norm_adjoint_comp_self,
        Real.norm_eq_abs]
      simpa only [pow_two] using
        add_le_add hDelta
          (le_refl (|a| *
            (‖cmp99OmegaSourcePhysicalOneStepQ Seq r rho U‖ *
              ‖cmp99OmegaSourcePhysicalOneStepQ Seq r rho U‖)))
    _ ≤ 16 / spacing ^ 2 + |a| := by
      have hQsq : ‖cmp99OmegaSourcePhysicalOneStepQ Seq r rho U‖ ^ 2 ≤ 1 := by
        nlinarith [norm_nonneg
          (cmp99OmegaSourcePhysicalOneStepQ Seq r rho U)]
      exact add_le_add le_rfl
        (by simpa using mul_le_mul_of_nonneg_left hQsq (abs_nonneg a))
    _ = cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound spacing a := rfl

/-- Positive coercivity constant generated by the physical one-step data. -/
noncomputable def cmp99OmegaSourcePhysicalOneStepCoercivityConstant
    (M : ℕ) (spacing a : ℝ) : ℝ :=
  min 1 a / cmp99OneScaleRegionalPhysicalPoincareConstant M spacing

theorem cmp99OmegaSourcePhysicalOneStepCoercivityConstant_pos
    {spacing a : ℝ} (ha : 0 < a) :
    0 < cmp99OmegaSourcePhysicalOneStepCoercivityConstant M spacing a := by
  unfold cmp99OmegaSourcePhysicalOneStepCoercivityConstant
  exact div_pos (lt_min zero_lt_one ha)
    (cmp99OneScaleRegionalPhysicalPoincareConstant_pos spacing)

/-- Exact physical one-step Green operator. -/
noncomputable def cmp99OmegaSourcePhysicalOneStepGreen
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :=
  covarianceOfIsCoerciveCLM
    (cmp99OmegaSourcePhysicalOneStepGaugePrecision
      Seq r rho U spacing a)
    (cmp99OmegaSourcePhysicalOneStepCoercivityConstant_pos ha)
    (coercive_cmp99OmegaSourcePhysicalOneStepGaugePrecision
      Seq r rho U hspacing ha.le)

theorem cmp99OmegaSourcePhysicalOneStepPrecision_comp_green
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    (cmp99OmegaSourcePhysicalOneStepGaugePrecision
      Seq r rho U spacing a).comp
        (cmp99OmegaSourcePhysicalOneStepGreen
          Seq r rho U hspacing ha) =
      ContinuousLinearMap.id ℝ _ := by
  exact precision_comp_covarianceOfIsCoerciveCLM _
    (cmp99OmegaSourcePhysicalOneStepCoercivityConstant_pos ha)
    (coercive_cmp99OmegaSourcePhysicalOneStepGaugePrecision
      Seq r rho U hspacing ha.le)

theorem cmp99OmegaSourcePhysicalOneStepGreen_comp_precision
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    (cmp99OmegaSourcePhysicalOneStepGreen Seq r rho U hspacing ha).comp
        (cmp99OmegaSourcePhysicalOneStepGaugePrecision
          Seq r rho U spacing a) =
      ContinuousLinearMap.id ℝ _ := by
  exact covarianceOfIsCoerciveCLM_comp_precision _
    (cmp99OmegaSourcePhysicalOneStepCoercivityConstant_pos ha)
    (coercive_cmp99OmegaSourcePhysicalOneStepGaugePrecision
      Seq r rho U hspacing ha.le)

theorem cmp99OmegaSourcePhysicalOneStepGreen_isSymmetric
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    (cmp99OmegaSourcePhysicalOneStepGreen
      Seq r rho U hspacing ha).IsSymmetric := by
  apply covarianceOfIsCoerciveCLM_isSymmetric
  have h := cmp99OmegaSourcePhysicalGaugePrecision_isSymmetric
    Seq r (cmp99OmegaSourcePhysicalOneStepTower Seq r rho U spacing) rho U a
  rw [cmp99OmegaSourcePhysicalGaugePrecision_oneStepTower_eq] at h
  exact h

/-- The literal weighted middle operator `Q' G'^2 Q'^dagger`. -/
noncomputable def cmp99OmegaSourcePhysicalOneStepCoarseCovarianceMiddle
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :=
  cmp99SourceTowerCoarseCovarianceMiddle
    (cmp99OmegaSourcePhysicalOneStepTower Seq r rho U spacing)
    (cmp99OmegaSourcePhysicalOneStepGreen Seq r rho U hspacing ha)

/-- The middle operator has the source-generated lower bound `Lambda^-2`. -/
theorem coercive_cmp99OmegaSourcePhysicalOneStepCoarseCovarianceMiddle
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    IsCoerciveCLM
      (cmp99OmegaSourcePhysicalOneStepCoarseCovarianceMiddle
        Seq r rho U hspacing ha)
      (cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound spacing a ^ 2)⁻¹ := by
  let T := cmp99OmegaSourcePhysicalOneStepTower Seq r rho U spacing
  let A := cmp99OmegaSourcePhysicalOneStepGaugePrecision
    Seq r rho U spacing a
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hterminal : 0 < T.terminalSpacing := by
    dsimp [T]
    positivity
  have hsymm : A.IsSymmetric := by
    have h := cmp99OmegaSourcePhysicalGaugePrecision_isSymmetric
      Seq r T rho U a
    rw [cmp99OmegaSourcePhysicalGaugePrecision_oneStepTower_eq] at h
    exact h
  exact isCoerciveCLM_cmp99SourceTowerCoarseCovarianceMiddle
    T A hspacing hterminal
    (cmp99OmegaSourcePhysicalOneStepCoercivityConstant_pos ha)
    (cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound_pos hspacing)
    (coercive_cmp99OmegaSourcePhysicalOneStepGaugePrecision
      Seq r rho U hspacing ha.le)
    hsymm
    (norm_cmp99OmegaSourcePhysicalOneStepGaugePrecision_le
      Seq r rho U hspacing)

/-- The one-step printed coarse covariance, with all inverse-existence inputs
generated from the physical source data. -/
noncomputable def cmp99OmegaSourcePhysicalOneStepCoarseCovariance
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :=
  covarianceOfIsCoerciveCLM
    (cmp99OmegaSourcePhysicalOneStepCoarseCovarianceMiddle
      Seq r rho U hspacing ha)
    (inv_pos.mpr (sq_pos_of_pos
      (cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound_pos hspacing)))
    (coercive_cmp99OmegaSourcePhysicalOneStepCoarseCovarianceMiddle
      Seq r rho U hspacing ha)

theorem cmp99OmegaSourcePhysicalOneStepCoarseCovariance_comp_middle
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    (cmp99OmegaSourcePhysicalOneStepCoarseCovariance
      Seq r rho U hspacing ha).comp
        (cmp99OmegaSourcePhysicalOneStepCoarseCovarianceMiddle
          Seq r rho U hspacing ha) =
      ContinuousLinearMap.id ℝ _ := by
  exact covarianceOfIsCoerciveCLM_comp_precision _
    (inv_pos.mpr (sq_pos_of_pos
      (cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound_pos hspacing)))
    (coercive_cmp99OmegaSourcePhysicalOneStepCoarseCovarianceMiddle
      Seq r rho U hspacing ha)

theorem cmp99OmegaSourcePhysicalOneStepMiddle_comp_coarseCovariance
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    (cmp99OmegaSourcePhysicalOneStepCoarseCovarianceMiddle
      Seq r rho U hspacing ha).comp
        (cmp99OmegaSourcePhysicalOneStepCoarseCovariance
          Seq r rho U hspacing ha) =
      ContinuousLinearMap.id ℝ _ := by
  exact precision_comp_covarianceOfIsCoerciveCLM _
    (inv_pos.mpr (sq_pos_of_pos
      (cmp99OmegaSourcePhysicalOneStepPrecisionUpperBound_pos hspacing)))
    (coercive_cmp99OmegaSourcePhysicalOneStepCoarseCovarianceMiddle
      Seq r rho U hspacing ha)

end

end YangMills.RG
