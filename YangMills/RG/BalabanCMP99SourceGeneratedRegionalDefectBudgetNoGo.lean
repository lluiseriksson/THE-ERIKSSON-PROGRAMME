/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedRegionalDefectContraction
import YangMills.RG.BalabanCMP99SourceEq395CorrectionOperatorNorm

/-!
# PRE-VALIDATION: no-go for the generated regional Schur budget

The source below is present, but its `.olean` has not yet been materialized
and its results have not yet been verified by the Lean compiler.

The step-7 contraction endpoint reduces `norm R' < 1` to one explicit Schur
budget.  At base depth that particular budget cannot be smaller than one.
The obstruction is quantitative and unconditional in the small-field radius:

* every source profile has `derivBound >= 3`, because it is one at `1/3` and
  zero at `2/3`;
* the explicit one-scale Poincare constant is at least `3 * M^4`;
* the generated inverse estimate pays the reciprocal coercivity; and
* both polynomial exponential shell sums contain their radius-zero term.

The theorem below concerns the *majorant*, not the physical operator.  It does
not prove `1 <= norm R'`; it proves that this coarse generated
Combes--Thomas/Schur route cannot certify the source contraction.  A faithful
continuation must instead retain the direct `O(M^-1)` estimate printed in
CMP99 (3.89), or prove an equivalent sharper weighted estimate.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

/-- Any profile satisfying the literal plateau and support conditions of
CMP95 (1.118) has derivative budget at least three. -/
theorem CMP95SourceSmoothPartitionProfile.three_le_derivBound
    (P : CMP95SourceSmoothPartitionProfile) :
    3 <= P.derivBound := by
  have hthird : P.value (1 / 3 : ℝ) = 1 :=
    P.plateau (1 / 3 : ℝ) (by constructor <;> norm_num)
  have htwoThirds : P.value (2 / 3 : ℝ) = 0 := by
    by_contra hne
    have hsupp : (2 / 3 : ℝ) ∈ Function.support P.value := hne
    have hinter := P.support_subset hsupp
    norm_num at hinter
  have hlip := P.norm_value_sub_value_le (1 / 3 : ℝ) (2 / 3 : ℝ)
  rw [htwoThirds, hthird] at hlip
  norm_num [Real.norm_eq_abs] at hlip
  linarith

variable {M : ℕ} [NeZero M]

/-- At depth zero the source-generated coercivity has its exact one-scale
form.  Exposing it keeps the cancellation with the Laplacian row auditable. -/
theorem cmp99SourceGeneratedCoercivity_depth_zero
    (M : ℕ) [NeZero M] (spacing epsilon : ℝ) :
    cmp99SourceGeneratedCoercivity 4 M 1 spacing epsilon =
      1 / (cmp99OneScaleBlockPoincareConstant 4 M * spacing ^ 2) := by
  simp [cmp99SourceGeneratedCoercivity,
    cmp99SourcePoincareErrorCoeff, cmp99SourcePoincareEnergyCoeff]

/-- The literal step-7 Schur budget is already enormous at base depth.

The numerical lower bound is deliberately inessential; its role is to make
the contradiction with `< 1` completely explicit. -/
theorem cmp99SourceGeneratedPhysicalRegionalDefectBudget_depth_zero_lower_bound
    (P : CMP95SourceSmoothPartitionProfile) (hM : 2 <= M)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing) :
    (11943936 : ℝ) <=
      cmp99SourceGeneratedPhysicalRegionalDefectBudget
        P M 0 spacing epsilon := by
  let CP := cmp99OneScaleBlockPoincareConstant 4 M
  let rate := cmp99SourceGeneratedPhysicalRegionalGreenRate M 0 spacing epsilon
  let defectRate := cmp99SourceGeneratedPhysicalRegionalDefectRate
    M 0 spacing epsilon
  let S := cmp99OmegaSiteExpSumBound defectRate
  let c := cmp99SourceGeneratedCoercivity 4 M 1 spacing epsilon
  let lap := cmp99SourceGeneratedPhysicalLargeBlockLaplacianBudget
    P M spacing rate
  let cutoff := cmp99SourceGeneratedPhysicalLargeBlockCutoffBudget
    P M 0 spacing epsilon rate

  have hsmall : cmp99SourcePoincareErrorCoeff 4 M 1 spacing epsilon < 1 := by
    simp [cmp99SourcePoincareErrorCoeff, cmp99SourcePoincareEnergyCoeff]
  have hrate : 0 < rate := by
    dsimp [rate]
    exact cmp99SourceGeneratedPhysicalRegionalGreenRate_pos
      M 0 hspacing hsmall
  have hdefectRate : 0 < defectRate := by
    dsimp [defectRate, cmp99SourceGeneratedPhysicalRegionalDefectRate]
    positivity
  have hS : 1 <= S := by
    dsimp [S]
    exact one_le_cmp99OmegaSiteExpSumBound hdefectRate
  have hc : c = 1 / (CP * spacing ^ 2) := by
    dsimp [c, CP]
    exact cmp99SourceGeneratedCoercivity_depth_zero M spacing epsilon
  have hCPpos : 0 < CP := by
    dsimp [CP]
    exact cmp99OneScaleBlockPoincareConstant_pos
  have hcpos : 0 < c := by
    rw [hc]
    positivity
  have hMreal : (2 : ℝ) <= M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le (by norm_num) hMreal
  have hM2 : (4 : ℝ) <= (M : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((M : ℝ) - 2)]
  have hM3 : (8 : ℝ) <= (M : ℝ) ^ 3 := by
    calc
      (8 : ℝ) = 2 * 4 := by norm_num
      _ <= (M : ℝ) * (M : ℝ) ^ 2 := by
        exact mul_le_mul hMreal hM2 (by norm_num) hMpos.le
      _ = (M : ℝ) ^ 3 := by ring
  have hCP : 3 * (M : ℝ) ^ 4 <= CP := by
    dsimp [CP, cmp99OneScaleBlockPoincareConstant]
    exact le_max_right _ _
  have hCPdiv : (24 : ℝ) <= CP / (M : ℝ) := by
    have hthree : 3 * (M : ℝ) ^ 3 <= CP / (M : ℝ) := by
      rw [le_div_iff₀ hMpos]
      calc
        3 * (M : ℝ) ^ 3 * (M : ℝ) = 3 * (M : ℝ) ^ 4 := by ring
        _ <= CP := hCP
    nlinarith
  have hderiv : (3 : ℝ) <= P.derivBound := P.three_le_derivBound
  have hexp : 1 <= Real.exp rate := Real.one_le_exp hrate.le
  have hlapNonneg : 0 <= lap := by
    dsimp [lap, cmp99SourceGeneratedPhysicalLargeBlockLaplacianBudget,
      cmp99ActiveRegionSourceCovariantLaplacianWeightedRowAmplitude]
    positivity
  have hmassNonneg :
      0 <= cmp99SourceGeneratedPhysicalLargeBlockMassBudget
        P M 0 spacing epsilon rate := by
    unfold cmp99SourceGeneratedPhysicalLargeBlockMassBudget
    positivity
  have hlapCutoff : lap <= cutoff := by
    dsimp [cutoff, cmp99SourceGeneratedPhysicalLargeBlockCutoffBudget]
    exact le_add_of_nonneg_right hmassNonneg
  have hlapProduct :
      lap * (2 / c) =
        10368 * P.derivBound * (CP / (M : ℝ)) * Real.exp rate := by
    dsimp [lap, cmp99SourceGeneratedPhysicalLargeBlockLaplacianBudget,
      cmp99ActiveRegionSourceCovariantLaplacianWeightedRowAmplitude]
    rw [hc]
    field_simp [ne_of_gt hMpos, ne_of_gt hspacing, ne_of_gt hCPpos]
    ring
  have hlower : (746496 : ℝ) <= lap * (2 / c) := by
    rw [hlapProduct]
    calc
      (746496 : ℝ) = 10368 * 3 * 24 * 1 := by norm_num
      _ <= 10368 * P.derivBound * 24 * 1 := by gcongr
      _ <= 10368 * P.derivBound * (CP / (M : ℝ)) * 1 := by
        gcongr
      _ <= 10368 * P.derivBound * (CP / (M : ℝ)) * Real.exp rate := by
        gcongr
  have hcutoffProduct :
      lap * (2 / c) <= cutoff * (2 / c) := by
    exact mul_le_mul_of_nonneg_right hlapCutoff (by positivity)
  calc
    (11943936 : ℝ) = 16 * (((746496 : ℝ) * 1) * 1) := by norm_num
    _ <= 16 * (((lap * (2 / c)) * S) * S) := by gcongr
    _ <= 16 * (((cutoff * (2 / c)) * S) * S) := by gcongr
    _ = cmp99SourceGeneratedPhysicalRegionalDefectBudget
          P M 0 spacing epsilon := by
      dsimp [cutoff, c, rate, defectRate, S]
      simp only [cmp99SourceGeneratedPhysicalRegionalDefectBudget,
        cmp99SourceGeneratedPhysicalRegionalDefectAmplitude,
        cmp99SourceGeneratedPhysicalRegionalCorrectionAmplitude,
        cmp99SourceGeneratedPhysicalRegionalDefectRate]
      ring

/-- The current generated Combes--Thomas/Schur majorant cannot inhabit the
fifteenth smallness window, already at base depth. -/
theorem not_cmp99SourceGeneratedPhysicalRegionalDefectBudget_lt_one_depth_zero
    (P : CMP95SourceSmoothPartitionProfile) (hM : 2 <= M)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing) :
    not (cmp99SourceGeneratedPhysicalRegionalDefectBudget
      P M 0 spacing epsilon < 1) := by
  have h := cmp99SourceGeneratedPhysicalRegionalDefectBudget_depth_zero_lower_bound
    P hM hspacing
  linarith

end

end YangMills.RG
