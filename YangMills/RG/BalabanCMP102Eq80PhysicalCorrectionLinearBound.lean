/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalCorrection
import YangMills.RG.BalabanCMP102PhysicalBackgroundZeroChart

/-!
# Linear stability of the physical CMP102 equation-(80) correction

The unique fixed point `D(A)` is compared with the normalized zero solution
using two charts generated from the same scalar source data.  Solving the
resulting contraction inequality gives the explicit, volume-uniform bound

`|D(A)|∞ ≤ L / (1 - L |H|∞) * |A|∞`.

No differentiability or continuity of the implicitly defined correction is
assumed.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d L N' Nc : ℕ}
variable [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
  [NeZero (L * N')]

omit [NeZero d] [NeZero L] [NeZero Nc] in
/-- The explicit physical correction rate is nonnegative on source chart
radii. -/
theorem cmp102PhysicalCorrectionContractionRate_nonneg
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    0 ≤ cmp102PhysicalCorrectionContractionRate Nc d L r s := by
  have hR0 := cmp98SourceLogAverageRadius_nonneg r hr
  have houter0 : 0 ≤ cmp98SourceOuterExpNormBudget r := by
    unfold cmp98SourceOuterExpNormBudget
    have hsecond :=
      expSecondDerivativeBudget_nonneg
        (cmp98SourceLogAverageRadius r) hR0
    have hfirst :=
      expDerivativeBudget_nonneg (cmp98SourceLogAverageRadius r) hR0
    positivity
  have hnearR := nearLogDerivativeBudget_nonneg r hr
  have hnearS := nearLogDerivativeBudget_nonneg s hs
  have hexpR := cmp102ExpLipschitzBudget_nonneg r hr
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

set_option maxHeartbeats 10000000 in
/-- **Linear stability of the source-defined physical fixed point.** -/
theorem cmp102Eq80PhysicalBackgroundCorrection_supNorm_le
    (U : PhysicalGaugeBackground d (L * N') Nc)
    {a CP ε : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget d Nc ε <
      min 1 a / CP)
    (ρ radius r s : FinePhysicalOneCochain d L N' Nc → ℝ)
    (S : ∀ A, CMP102PhysicalBackgroundCorrectionScalarData
      U ha hP hε hsmall hbudget A (ρ A) (radius A) (r A) (s A))
    (hcontract : ∀ A, ((S A).toBallData).contractionRate < 1)
    (A : FinePhysicalOneCochain d L N' Nc) :
    cmp102PhysicalCorrectionSupNorm
        (cmp102Eq80PhysicalBackgroundCorrection
          U ha hP hε hsmall hbudget ρ radius r s S hcontract A) ≤
      (cmp102PhysicalCorrectionContractionRate Nc d L (r A) (s A) /
          (1 - ((S A).toBallData).contractionRate)) *
        cmp98SourceFieldSupNorm A := by
  let Dsup :=
    Classical.choose ((S A).existsUnique_backgroundCorrection
      (hcontract A))
  let D : CoarsePhysicalOneCochain d N' Nc :=
    physicalGaugeOneCochainSupEquiv.symm Dsup
  have hspec :=
    Classical.choose_spec
      ((S A).existsUnique_backgroundCorrection (hcontract A))
  have hDmem : ‖Dsup‖ ≤ ρ A := hspec.1.1
  let X : FinePhysicalOneCochain d L N' Nc :=
    A - cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget D
  let BX : CMP102PhysicalNonlinearChartBudget U X :=
    (S A).toBallData.chartBudget Dsup hDmem
  let B0 : CMP102PhysicalNonlinearChartBudget
      U (0 : FinePhysicalOneCochain d L N' Nc) :=
    (S A).zeroChartBudget
  have hfixed :
      cmp102PhysicalNonlinearCorrectionOfBudget U X BX = D := by
    have h := cmp102Eq80PhysicalBackgroundCorrection_eq
      U ha hP hε hsmall hbudget ρ radius r s S hcontract A
    simpa [Dsup, D, X, BX,
      cmp102Eq80PhysicalBackgroundCorrection] using h
  have honeX : |(1 : ℝ)| < BX.radius := by
    simpa using BX.one_lt_radius
  have hone0 : |(1 : ℝ)| < B0.radius := by
    simpa using B0.one_lt_radius
  have hcorr :=
    cmp102PhysicalCorrectionSupNorm_sub_le
      U X 0 BX.toFieldChart B0.toFieldChart (r A) (s A)
      BX.base
      (by simpa [X] using BX.small 1 honeX)
      (by simp)
      (by simpa [X, BX] using BX.localRadius 1 honeX)
      (by simpa [B0] using B0.localRadius 1 hone0)
      (S A).r_lt_one
      (by simpa [X, BX] using BX.relativeRadius 1 honeX)
      (by simpa [B0] using B0.relativeRadius 1 hone0)
      (S A).s_lt_one
  have hcorrBudget :
      cmp102PhysicalCorrectionSupNorm
          (cmp102PhysicalNonlinearCorrectionOfBudget U X BX -
            cmp102PhysicalNonlinearCorrectionOfBudget U 0 B0) ≤
        cmp102PhysicalCorrectionContractionRate Nc d L (r A) (s A) *
          cmp98SourceFieldSupNorm (X - 0) := by
    simpa [cmp102PhysicalNonlinearCorrectionOfBudget] using hcorr
  rw [hfixed, cmp102PhysicalNonlinearCorrectionOfBudget_zero,
    sub_zero] at hcorrBudget
  have hH :=
    cmp98SourceFieldSupNorm_cmp99SourceEq3126PhysicalH_le
      U ha hP hε hsmall hbudget D
  have hsource :
      cmp98SourceFieldSupNorm X ≤
        cmp98SourceFieldSupNorm A +
          cmp99SourceEq3126PhysicalHSourceSupNorm
            U ha hP hε hsmall hbudget *
            cmp102PhysicalCorrectionSupNorm D := by
    exact (cmp98SourceFieldSupNorm_sub_le A
      (cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget D)).trans
        (add_le_add (le_refl _) hH)
  let Lrate := cmp102PhysicalCorrectionContractionRate
    Nc d L (r A) (s A)
  let Hrate := cmp99SourceEq3126PhysicalHSourceSupNorm
    U ha hP hε hsmall hbudget
  have hL : 0 ≤ Lrate := by
    exact cmp102PhysicalCorrectionContractionRate_nonneg
      (r A) (s A) (S A).r_nonneg (S A).s_nonneg
  have hcombined :
      cmp102PhysicalCorrectionSupNorm D ≤
        Lrate * (cmp98SourceFieldSupNorm A +
          Hrate * cmp102PhysicalCorrectionSupNorm D) := by
    have hsource' :
        cmp98SourceFieldSupNorm (X - 0) ≤
          cmp98SourceFieldSupNorm A +
            Hrate * cmp102PhysicalCorrectionSupNorm D := by
      simpa [Hrate] using hsource
    exact hcorrBudget.trans (mul_le_mul_of_nonneg_left hsource' hL)
  have hrate :
      ((S A).toBallData).contractionRate = Lrate * Hrate := by
    rfl
  have hsmallRate : Lrate * Hrate < 1 := by
    simpa [hrate] using hcontract A
  have hdenom : 0 < 1 - Lrate * Hrate := sub_pos.mpr hsmallRate
  have hlinear :
      (1 - Lrate * Hrate) * cmp102PhysicalCorrectionSupNorm D ≤
        Lrate * cmp98SourceFieldSupNorm A := by
    nlinarith
  have hbound :
      cmp102PhysicalCorrectionSupNorm D ≤
        (Lrate / (1 - Lrate * Hrate)) *
          cmp98SourceFieldSupNorm A := by
    calc
      cmp102PhysicalCorrectionSupNorm D ≤
          (Lrate * cmp98SourceFieldSupNorm A) /
            (1 - Lrate * Hrate) :=
        (le_div_iff₀ hdenom).2 (by simpa [mul_comm] using hlinear)
      _ = (Lrate / (1 - Lrate * Hrate)) *
          cmp98SourceFieldSupNorm A := by ring
  simpa [D, Dsup, Lrate, Hrate, hrate,
    cmp102Eq80PhysicalBackgroundCorrection] using hbound

end

end YangMills.RG
