/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalHSupNorm
import YangMills.RG.BalabanCMP102PhysicalCorrectionContraction

/-!
# Lipschitz bound for the physical CMP102 background-correction map

CMP102 determines the nonlinear background correction from the map

`D ↦ C(A - H D)`.

This module composes the already physical two-field bound for `C` with the
literal auxiliary CMP99 equation-(3.126) minimizer `H`.  The resulting
Lipschitz constant is the product of two constructed quantities:

* the explicit CMP102 correction rate;
* the genuine source-sup operator norm of the physical `H`.

No Lipschitz estimate for the composite map is supplied by the caller.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

/-- Subtracting two fields shifted by the physical CMP99 minimizer costs its
actual source-sup operator norm. -/
theorem cmp98SourceFieldSupNorm_physicalHShift_sub_le
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (A : PhysicalGaugeOneCochain d (L * N') Nc)
    (D₁ D₂ : CoarsePhysicalOneCochain d N' Nc) :
    cmp98SourceFieldSupNorm
        ((A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget D₁) -
          (A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget D₂)) ≤
      cmp99SourceEq3126PhysicalHSourceSupNorm
          U ha hP hε hsmall hbudget *
        cmp102PhysicalCorrectionSupNorm (D₂ - D₁) := by
  have hfield :
      (A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget D₁) -
          (A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget D₂) =
        cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget (D₂ - D₁) := by
    rw [map_sub]
    abel
  rw [hfield]
  exact cmp98SourceFieldSupNorm_cmp99SourceEq3126PhysicalH_le
    U ha hP hε hsmall hbudget (D₂ - D₁)

set_option maxHeartbeats 15000000 in
/-- **Physical composite Lipschitz bound.**  The nonlinear corrections at
`A - H D₁` and `A - H D₂` contract with the explicit composite rate.  The
chart packages only certify that the two literal logarithmic expressions
are defined; chart independence has already shown that they do not alter
the values. -/
theorem cmp102PhysicalBackgroundCorrectionSupNorm_sub_le
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (A : PhysicalGaugeOneCochain d (L * N') Nc)
    (D₁ D₂ : CoarsePhysicalOneCochain d N' Nc)
    (B₁ : CMP102PhysicalNonlinearChartBudget U
      (A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget D₁))
    (B₂ : CMP102PhysicalNonlinearChartBudget U
      (A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget D₂))
    (r s : ℝ)
    (hlocal₁ : B₁.localNoWinding.δ = r)
    (hlocal₂ : B₂.localNoWinding.δ = r)
    (hrelative₁ : B₁.relativeNoWinding.δ = s)
    (hrelative₂ : B₂.relativeNoWinding.δ = s) :
    cmp102PhysicalCorrectionSupNorm
        (cmp102PhysicalNonlinearCorrectionOfBudget U
            (A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget D₁) B₁ -
          cmp102PhysicalNonlinearCorrectionOfBudget U
            (A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget D₂) B₂) ≤
      (cmp102PhysicalCorrectionContractionRate Nc d L r s *
          cmp99SourceEq3126PhysicalHSourceSupNorm
            U ha hP hε hsmall hbudget) *
        cmp102PhysicalCorrectionSupNorm (D₂ - D₁) := by
  let X :=
    A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget D₁
  let Y :=
    A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget D₂
  have hone₁ : |(1 : ℝ)| < B₁.radius := by
    simpa using B₁.one_lt_radius
  have hone₂ : |(1 : ℝ)| < B₂.radius := by
    simpa using B₂.one_lt_radius
  have hX : cmp98SourceFieldSupNorm X ≤ 1 / 2 := by
    simpa [X] using B₁.small 1 hone₁
  have hY : cmp98SourceFieldSupNorm Y ≤ 1 / 2 := by
    simpa [Y] using B₂.small 1 hone₂
  have hrX : 1 / 3 + cmp98SourceContourDisplacementBudget X 1 ≤ r := by
    simpa [X, hlocal₁] using B₁.localRadius 1 hone₁
  have hrY : 1 / 3 + cmp98SourceContourDisplacementBudget Y 1 ≤ r := by
    simpa [Y, hlocal₂] using B₂.localRadius 1 hone₂
  have hr1 : r < 1 := by
    simpa [← hlocal₁] using B₁.localNoWinding.δ_lt_one
  have hsX : cmp98SourcePhysicalBlockDisplacementBudget X 1 r ≤ s := by
    simpa [X, hlocal₁, hrelative₁] using B₁.relativeRadius 1 hone₁
  have hsY : cmp98SourcePhysicalBlockDisplacementBudget Y 1 r ≤ s := by
    simpa [Y, hlocal₂, hrelative₂] using B₂.relativeRadius 1 hone₂
  have hs1 : s < 1 := by
    simpa [← hrelative₁] using B₁.relativeNoWinding.δ_lt_one
  have hr13 : (1 / 3 : ℝ) ≤ r := by
    exact (le_add_of_nonneg_right
      (cmp98SourceContourDisplacementBudget_nonneg X 1)).trans hrX
  have hr0 : 0 ≤ r := (by norm_num : (0 : ℝ) ≤ 1 / 3).trans hr13
  have hR0 : 0 ≤ cmp98SourceLogAverageRadius r :=
    cmp98SourceLogAverageRadius_nonneg r hr0
  have houter0 : 0 ≤ cmp98SourceOuterExpNormBudget r := by
    unfold cmp98SourceOuterExpNormBudget
    have hsecond :=
      expSecondDerivativeBudget_nonneg
        (cmp98SourceLogAverageRadius r) hR0
    have hfirst :=
      expDerivativeBudget_nonneg (cmp98SourceLogAverageRadius r) hR0
    positivity
  have houterDisp0 :
      0 ≤ cmp98SourceOuterExpDisplacementBudget X 1 r := by
    unfold cmp98SourceOuterExpDisplacementBudget
    have hsecond :=
      expSecondDerivativeBudget_nonneg
        (cmp98SourceLogAverageRadius r) hR0
    have hfirst :=
      expDerivativeBudget_nonneg (cmp98SourceLogAverageRadius r) hR0
    have hdisp :=
      cmp98SourceLogAverageDisplacementBudget_nonneg X 1 r hr0
    positivity
  have hcoarse0 :
      0 ≤ cmp98SourceCoarseContourDisplacementBudget X 1 :=
    cmp98SourceCoarseContourDisplacementBudget_nonneg X 1
  have hblock0 :
      0 ≤ cmp98SourcePhysicalBlockDisplacementBudget X 1 r := by
    unfold cmp98SourcePhysicalBlockDisplacementBudget
    positivity
  have hs0 : 0 ≤ s := hblock0.trans hsX
  have hcorrection :
      cmp102PhysicalCorrectionSupNorm
          (cmp102PhysicalNonlinearCorrectionOfBudget U X B₁ -
            cmp102PhysicalNonlinearCorrectionOfBudget U Y B₂) ≤
        cmp102PhysicalCorrectionContractionRate Nc d L r s *
          cmp98SourceFieldSupNorm (X - Y) := by
    exact cmp102PhysicalCorrectionSupNorm_sub_le
      U X Y B₁.toFieldChart B₂.toFieldChart r s
      B₁.base hX hY hrX hrY hr1 hsX hsY hs1
  have hshift :
      cmp98SourceFieldSupNorm (X - Y) ≤
        cmp99SourceEq3126PhysicalHSourceSupNorm
            U ha hP hε hsmall hbudget *
          cmp102PhysicalCorrectionSupNorm (D₂ - D₁) := by
    simpa [X, Y] using
      cmp98SourceFieldSupNorm_physicalHShift_sub_le
        U ha hP hε hsmall hbudget A D₁ D₂
  have hrate :
      0 ≤ cmp102PhysicalCorrectionContractionRate Nc d L r s := by
    have hnearR := nearLogDerivativeBudget_nonneg r hr0
    have hnearS := nearLogDerivativeBudget_nonneg s hs0
    have hexpR := cmp102ExpLipschitzBudget_nonneg r hr0
    have hexpLogR :=
      cmp102ExpLipschitzBudget_nonneg
        (cmp98SourceLogAverageRadius r) hR0
    have hexpHalf :=
      cmp102ExpLipschitzBudget_nonneg (1 / 2) (by norm_num)
    unfold cmp102PhysicalCorrectionContractionRate
      cmp102SourceCorrectionLinearRate
      cmp102SourceLogCorrectionLinearRate
      cmp102SourceRightVariationLinearRate
    positivity
  calc
    cmp102PhysicalCorrectionSupNorm
          (cmp102PhysicalNonlinearCorrectionOfBudget U X B₁ -
            cmp102PhysicalNonlinearCorrectionOfBudget U Y B₂)
        ≤ cmp102PhysicalCorrectionContractionRate Nc d L r s *
            cmp98SourceFieldSupNorm (X - Y) := hcorrection
    _ ≤ cmp102PhysicalCorrectionContractionRate Nc d L r s *
          (cmp99SourceEq3126PhysicalHSourceSupNorm
              U ha hP hε hsmall hbudget *
            cmp102PhysicalCorrectionSupNorm (D₂ - D₁)) :=
      mul_le_mul_of_nonneg_left hshift hrate
    _ = (cmp102PhysicalCorrectionContractionRate Nc d L r s *
          cmp99SourceEq3126PhysicalHSourceSupNorm
            U ha hP hε hsmall hbudget) *
        cmp102PhysicalCorrectionSupNorm (D₂ - D₁) := by ring

end

end YangMills.RG
