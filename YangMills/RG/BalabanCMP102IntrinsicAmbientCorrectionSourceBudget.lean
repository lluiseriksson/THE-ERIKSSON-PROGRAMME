/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102AmbientNonlinearBlockSourceBudget
import YangMills.RG.BalabanCMP102IntrinsicAmbientCorrectionFDeriv
import YangMills.RG.BalabanCMP98Eq123PhysicalBlockBound

/-!
# Source-generated inputs for the intrinsic ambient correction

The right normalizer is fixed at the background.  This module uses the exact
background identity and the source bound for that normalizer to turn the
represented-block value-Lipschitz estimate into relative-deviation value and
Lipschitz budgets.  It then feeds those budgets, together with the generated
block derivative budgets, into the intrinsic-correction derivative theorem.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Source-generated Lipschitz budget after exact right normalization. -/
def cmp102SourceAmbientRelativeDeviationLipschitzBudget
    (d M : ℕ) (r q : ℝ) : ℝ :=
  cmp102SourceAmbientNonlinearBlockValueLipschitzBudget d M r q *
    cmp98SourceOuterExpNormBudget q

/-- Source-generated relative-deviation radius on the ambient `r`-ball. -/
def cmp102SourceAmbientRelativeDeviationValueBudget
    (d M : ℕ) (r q : ℝ) : ℝ :=
  cmp102SourceAmbientRelativeDeviationLipschitzBudget d M r q * r

/-- Fully generated derivative-Lipschitz budget for the intrinsic correction. -/
def cmp102SourceIntrinsicAmbientCorrectionDerivativeLipschitzBudget
    (d M : ℕ) (r q s : ℝ) : ℝ :=
  cmp102IntrinsicAmbientCorrectionDerivativeLipschitzBudget
    s
    (cmp102SourceAmbientRelativeDeviationLipschitzBudget d M r q)
    (cmp102SourceAmbientNonlinearBlockDerivativeBudget d M r q)
    (cmp102SourceAmbientNonlinearBlockDerivativeLipschitzBudget d M r q)
    (cmp98SourceOuterExpNormBudget q)

theorem cmp98SourceOuterExpNormBudget_nonneg_of_nonneg
    {q : ℝ} (hq0 : 0 ≤ q) :
    0 ≤ cmp98SourceOuterExpNormBudget q := by
  unfold cmp98SourceOuterExpNormBudget
  have hR := cmp98SourceLogAverageRadius_nonneg q hq0
  have hB₂ := expSecondDerivativeBudget_nonneg _ hR
  have hB₁ := expDerivativeBudget_nonneg _ hR
  positivity

theorem cmp102SourceAmbientRelativeDeviationLipschitzBudget_nonneg
    {d M : ℕ} {r q : ℝ} (hr : 0 ≤ r) (hq0 : 0 ≤ q) :
    0 ≤ cmp102SourceAmbientRelativeDeviationLipschitzBudget d M r q := by
  unfold cmp102SourceAmbientRelativeDeviationLipschitzBudget
  exact mul_nonneg
    (cmp102SourceAmbientNonlinearBlockValueLipschitzBudget_nonneg hr hq0)
    (cmp98SourceOuterExpNormBudget_nonneg_of_nonneg hq0)

theorem cmp102SourceAmbientRelativeDeviationValueBudget_nonneg
    {d M : ℕ} {r q : ℝ} (hr : 0 ≤ r) (hq0 : 0 ≤ q) :
    0 ≤ cmp102SourceAmbientRelativeDeviationValueBudget d M r q := by
  unfold cmp102SourceAmbientRelativeDeviationValueBudget
  exact mul_nonneg
    (cmp102SourceAmbientRelativeDeviationLipschitzBudget_nonneg hr hq0) hr

theorem cmp102SourceIntrinsicAmbientCorrectionDerivativeLipschitzBudget_nonneg
    {d M : ℕ} {r q s : ℝ} (hr : 0 ≤ r) (hq0 : 0 ≤ q) (hs0 : 0 ≤ s) :
    0 ≤ cmp102SourceIntrinsicAmbientCorrectionDerivativeLipschitzBudget
      d M r q s := by
  unfold cmp102SourceIntrinsicAmbientCorrectionDerivativeLipschitzBudget
    cmp102IntrinsicAmbientCorrectionDerivativeLipschitzBudget
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (nearLogSecondDerivativeBudget_nonneg s hs0)
          (cmp102SourceAmbientRelativeDeviationLipschitzBudget_nonneg hr hq0))
        (cmp102SourceAmbientNonlinearBlockDerivativeBudget_nonneg hr hq0))
      (cmp98SourceOuterExpNormBudget_nonneg_of_nonneg hq0))
    (mul_nonneg
      (mul_nonneg (nearLogDerivativeBudget_nonneg s hs0)
        (cmp102SourceAmbientNonlinearBlockDerivativeLipschitzBudget_nonneg
          hr hq0))
      (cmp98SourceOuterExpNormBudget_nonneg_of_nonneg hq0))

private theorem cmp102AmbientNonlinearBlock_zero_mul_inverseAtZero
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N') :
    cmp102AmbientNonlinearBlock U b 0 *
        cmp98Eq119NonlinearBlockInverseAtZero U
          (0 : PhysicalGaugeOneCochain d (M * N') Nc) b = 1 := by
  have hline :=
    cmp102AmbientNonlinearBlock_physicalLine_eq U
      (0 : PhysicalGaugeOneCochain d (M * N') Nc) b 0
  have hzero :
      (0 : ℝ) • physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent
            (0 : PhysicalGaugeOneCochain d (M * N') Nc)) = 0 := by
    funext e i j
    simp [Pi.smul_apply]
  rw [hzero] at hline
  rw [hline]
  exact cmp98Eq119NonlinearBlockCurve_zero_mul_inverseAtZero U 0 b

/-- Exact right normalization turns the generated block difference into a
source-generated relative-deviation Lipschitz estimate. -/
theorem norm_cmp102AmbientRelativeDeviation_sub_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z W : PhysicalAmbientMatrixTangent d (M * N') Nc)
    {r q : ℝ} (hr : 0 ≤ r) (hq13 : 1 / 3 ≤ q) (hq1 : q < 1)
    (hZ : ‖Z‖ ≤ r) (hW : ‖W‖ ≤ r)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hDZ : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ ≤ q)
    (hDW : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x W‖ ≤ q) :
    ‖(cmp102AmbientNonlinearBlock U b Z *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : PhysicalGaugeOneCochain d (M * N') Nc) b - 1) -
        (cmp102AmbientNonlinearBlock U b W *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : PhysicalGaugeOneCochain d (M * N') Nc) b - 1)‖ ≤
      cmp102SourceAmbientRelativeDeviationLipschitzBudget d M r q *
        ‖Z - W‖ := by
  let I := cmp98Eq119NonlinearBlockInverseAtZero U
    (0 : PhysicalGaugeOneCochain d (M * N') Nc) b
  have hq0 : 0 ≤ q := (by norm_num : (0 : ℝ) ≤ 1 / 3).trans hq13
  have hblock :
      ‖cmp102AmbientNonlinearBlock U b Z -
          cmp102AmbientNonlinearBlock U b W‖ ≤
        cmp102SourceAmbientNonlinearBlockValueLipschitzBudget d M r q *
          ‖Z - W‖ :=
    norm_cmp102AmbientNonlinearBlock_sub_le_sourceBudget
      U b Z W hr hq0 hq1 hZ hW hDZ hDW
  have hI : ‖I‖ ≤ cmp98SourceOuterExpNormBudget q := by
    simpa [I] using
      norm_cmp98Eq119NonlinearBlockInverseAtZero_le_sourceBudget
        U (0 : PhysicalGaugeOneCochain d (M * N') Nc) b q
          hbase hq13 hq1
  have halg :
      (cmp102AmbientNonlinearBlock U b Z * I - 1) -
          (cmp102AmbientNonlinearBlock U b W * I - 1) =
        (cmp102AmbientNonlinearBlock U b Z -
          cmp102AmbientNonlinearBlock U b W) * I := by
    noncomm_ring
  change ‖(cmp102AmbientNonlinearBlock U b Z * I - 1) -
      (cmp102AmbientNonlinearBlock U b W * I - 1)‖ ≤ _
  rw [halg]
  calc
    ‖(cmp102AmbientNonlinearBlock U b Z -
          cmp102AmbientNonlinearBlock U b W) * I‖
        ≤ ‖cmp102AmbientNonlinearBlock U b Z -
              cmp102AmbientNonlinearBlock U b W‖ * ‖I‖ :=
      norm_mul_le _ _
    _ ≤
        (cmp102SourceAmbientNonlinearBlockValueLipschitzBudget d M r q *
          ‖Z - W‖) * cmp98SourceOuterExpNormBudget q := by
      exact mul_le_mul hblock hI (norm_nonneg I)
        (mul_nonneg
          (cmp102SourceAmbientNonlinearBlockValueLipschitzBudget_nonneg
            hr hq0)
          (norm_nonneg _))
    _ = cmp102SourceAmbientRelativeDeviationLipschitzBudget d M r q *
          ‖Z - W‖ := by
      unfold cmp102SourceAmbientRelativeDeviationLipschitzBudget
      ring

/-- The relative deviation itself lies in the generated source ball. -/
theorem norm_cmp102AmbientRelativeDeviation_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z : PhysicalAmbientMatrixTangent d (M * N') Nc)
    {r q : ℝ} (hr : 0 ≤ r) (hq13 : 1 / 3 ≤ q) (hq1 : q < 1)
    (hZ : ‖Z‖ ≤ r)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hDZ : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ ≤ q) :
    ‖cmp102AmbientNonlinearBlock U b Z *
        cmp98Eq119NonlinearBlockInverseAtZero U
          (0 : PhysicalGaugeOneCochain d (M * N') Nc) b - 1‖ ≤
      cmp102SourceAmbientRelativeDeviationValueBudget d M r q := by
  have hq0 : 0 ≤ q := (by norm_num : (0 : ℝ) ≤ 1 / 3).trans hq13
  have hD0 : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ q :=
    fun x hx => (hbase x hx).trans hq13
  have hdiff :=
    norm_cmp102AmbientRelativeDeviation_sub_le_sourceBudget
      U b Z 0 hr hq13 hq1 hZ (by simpa using hr)
        hbase hDZ hD0
  rw [cmp102AmbientNonlinearBlock_zero_mul_inverseAtZero U b,
    sub_self] at hdiff
  have hdiff' :
      ‖cmp102AmbientNonlinearBlock U b Z *
          cmp98Eq119NonlinearBlockInverseAtZero U
            (0 : PhysicalGaugeOneCochain d (M * N') Nc) b - 1‖ ≤
        cmp102SourceAmbientRelativeDeviationLipschitzBudget d M r q *
          ‖Z‖ := by
    simpa using hdiff
  unfold cmp102SourceAmbientRelativeDeviationValueBudget
  exact hdiff'.trans
    (mul_le_mul_of_nonneg_left hZ
      (cmp102SourceAmbientRelativeDeviationLipschitzBudget_nonneg hr hq0))

/-- All represented-block, relative-deviation, and normalizer estimates are
generated internally before applying the intrinsic correction theorem. -/
theorem norm_fderiv_cmp102IntrinsicAmbientCorrectionBond_sub_apply_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (b : PhysicalBond d N')
    (Z W H : PhysicalAmbientMatrixTangent d (M * N') Nc)
    {r q s : ℝ}
    (hr : 0 ≤ r) (hq13 : 1 / 3 ≤ q) (hq1 : q < 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hZ : ‖Z‖ ≤ r) (hW : ‖W‖ ≤ r)
    (hbase : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hDZ : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x Z‖ ≤ q)
    (hDW : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x W‖ ≤ q)
    (hdev :
      cmp102SourceAmbientRelativeDeviationValueBudget d M r q ≤ s) :
    ‖(fderiv ℝ (cmp102IntrinsicAmbientCorrectionBond U b) Z -
        fderiv ℝ (cmp102IntrinsicAmbientCorrectionBond U b) W) H‖ ≤
      cmp102SourceIntrinsicAmbientCorrectionDerivativeLipschitzBudget
          d M r q s *
        ‖Z - W‖ * ‖H‖ := by
  have hq0 : 0 ≤ q := (by norm_num : (0 : ℝ) ≤ 1 / 3).trans hq13
  apply norm_fderiv_cmp102IntrinsicAmbientCorrectionBond_sub_apply_le
    U b Z W H hs0 hs1
    (cmp102SourceAmbientRelativeDeviationLipschitzBudget_nonneg hr hq0)
    (cmp102SourceAmbientNonlinearBlockDerivativeBudget_nonneg hr hq0)
    (cmp102SourceAmbientNonlinearBlockDerivativeLipschitzBudget_nonneg hr hq0)
  · intro x hx
    exact (hDZ x hx).trans_lt hq1
  · intro x hx
    exact (hDW x hx).trans_lt hq1
  · exact (norm_cmp102AmbientRelativeDeviation_le_sourceBudget
      U b Z hr hq13 hq1 hZ hbase hDZ).trans hdev
  · exact (norm_cmp102AmbientRelativeDeviation_le_sourceBudget
      U b W hr hq13 hq1 hW hbase hDW).trans hdev
  · exact norm_cmp102AmbientRelativeDeviation_sub_le_sourceBudget
      U b Z W hr hq13 hq1 hZ hW hbase hDZ hDW
  · exact norm_fderiv_cmp102AmbientNonlinearBlock_le_sourceBudget
      U b Z hr hq0 hq1 hZ hDZ
  · exact norm_fderiv_cmp102AmbientNonlinearBlock_sub_le_sourceBudget
      U b Z W hr hq0 hq1 hZ hW hDZ hDW
  · exact norm_cmp98Eq119NonlinearBlockInverseAtZero_le_sourceBudget
      U (0 : PhysicalGaugeOneCochain d (M * N') Nc) b q
        hbase hq13 hq1

end

end YangMills.RG
