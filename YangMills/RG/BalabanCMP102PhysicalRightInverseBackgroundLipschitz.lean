/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalExpAverageBackgroundLipschitz
import YangMills.RG.BalabanCMP102IntrinsicAmbientCorrectionSourceBudget

/-!
# Background Lipschitz control of the CMP98 right inverse

The literal right normalization in CMP98 equation (119) is

`C(U)† * exp(-Y(U))`.

This module compares it with the same expression at the trivial background.
The proof is the exact two-factor telescope.  Its two inputs are already
physical:

* the straight coarse contour changes by at most `M * ε`;
* the normalized logarithmic average changes by the source-scale budget.

No norm certificate for the assembled inverse is supplied by the caller and
no periodic-volume cardinality occurs.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

set_option maxHeartbeats 2000000

local instance cmp102PhysicalRightInverseBackgroundMatrixNormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- Generated source-scale budget for the literal right inverse. -/
def cmp102PhysicalRightInverseBackgroundBudget
    (d M : ℕ) (r ε : ℝ) : ℝ :=
  (M : ℝ) * ε * cmp98SourceOuterExpNormBudget r +
    cmp102PhysicalExpAverageBackgroundValueBudget d M r ε

theorem cmp102PhysicalRightInverseBackgroundBudget_nonneg
    {d M : ℕ} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 ≤ ε) :
    0 ≤ cmp102PhysicalRightInverseBackgroundBudget d M r ε := by
  unfold cmp102PhysicalRightInverseBackgroundBudget
  apply add_nonneg
  · exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg M) hε)
      (cmp98SourceOuterExpNormBudget_nonneg_of_nonneg hr)
  · exact cmp102PhysicalExpAverageBackgroundValueBudget_nonneg hr hε

/-- The exact right inverse in CMP98 equation (119) is background-Lipschitz
with an explicit constant independent of the periodic volume. -/
theorem
    norm_cmp98Eq119NonlinearBlockInverseAtZero_sub_trivial_le_sourceScale
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (ε r : ℝ) (hε : 0 ≤ ε) (hr13 : 1 / 3 ≤ r) (hr1 : r < 1)
    (hsmall : PhysicalWilsonSmallBackground U ε)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N')
    (hbaseU : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hbase0 : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix
        (trivialPhysicalGaugeBackground d (M * N') Nc) b x 0‖ ≤ 1 / 3) :
    ‖cmp98Eq119NonlinearBlockInverseAtZero U A b -
        cmp98Eq119NonlinearBlockInverseAtZero
          (trivialPhysicalGaugeBackground d (M * N') Nc) A b‖ ≤
      cmp102PhysicalRightInverseBackgroundBudget d M r ε := by
  let U0 := trivialPhysicalGaugeBackground d (M * N') Nc
  let CU := cmp98ContourMatrixCurve U A
    (cmp98SourceCoarseBondPath (Nc := Nc) b) 0
  let C0 := cmp98ContourMatrixCurve U0 A
    (cmp98SourceCoarseBondPath (Nc := Nc) b) 0
  let YU := cmp98UbarLogAverage U b 0
  let Y0 := cmp98UbarLogAverage U0 b 0
  let EU := NormedSpace.exp (-YU)
  let E0 := NormedSpace.exp (-Y0)
  let R := cmp102SourceLogAverageRadius r
  let O := cmp98SourceOuterExpNormBudget r
  have hr0 : 0 ≤ r := (by norm_num : (0 : ℝ) ≤ 1 / 3).trans hr13
  have hbaseUr : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ r :=
    fun x hx => (hbaseU x hx).trans hr13
  have hbase0r : ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U0 b x 0‖ ≤ r :=
    fun x hx => (hbase0 x hx).trans hr13
  have hYU : ‖YU‖ ≤ R := by
    simpa only [YU, R] using
      norm_cmp98UbarLogAverage_le_sourceBudget U b 0 hr0 hr1 hbaseUr
  have hY0 : ‖Y0‖ ≤ R := by
    simpa only [Y0, U0, R] using
      norm_cmp98UbarLogAverage_le_sourceBudget U0 b 0 hr0 hr1 hbase0r
  have hYdiff :
      ‖YU - Y0‖ ≤
        cmp102PhysicalLogAverageBackgroundValueBudget d M r ε := by
    simpa only [YU, Y0, U0] using
      norm_cmp98UbarLogAverage_zero_sub_trivial_le_sourceScale
        U ε r hε hr0 hr1 hsmall b hbaseUr hbase0r
  have hEU : ‖EU‖ ≤ O := by
    have hneg : ‖-YU‖ ≤ R := by simpa using hYU
    have hraw := norm_exp_le_derivativeBudgets
      (cmp102SourceLogAverageRadius_nonneg hr0) hneg
    simpa [EU, O, cmp98SourceOuterExpNormBudget, R] using hraw
  have hEdiff :
      ‖EU - E0‖ ≤
        cmp102PhysicalExpAverageBackgroundValueBudget d M r ε := by
    have hnegYU : ‖-YU‖ ≤ R := by simpa using hYU
    have hnegY0 : ‖-Y0‖ ≤ R := by simpa using hY0
    have hraw :
        ‖NormedSpace.exp (-YU) - NormedSpace.exp (-Y0)‖ ≤
          cmp102ExpLipschitzBudget R * ‖-YU - -Y0‖ :=
      norm_exp_sub_exp_le_cmp102ExpLipschitzBudget
        (cmp102SourceLogAverageRadius_nonneg hr0) hnegYU hnegY0
    have hneg :
        ‖-YU - -Y0‖ ≤
          cmp102PhysicalLogAverageBackgroundValueBudget d M r ε := by
      calc
        ‖-YU - -Y0‖ = ‖YU - Y0‖ := by
          rw [← norm_neg]
          congr 1
          abel
        _ ≤ cmp102PhysicalLogAverageBackgroundValueBudget d M r ε := hYdiff
    change ‖NormedSpace.exp (-YU) - NormedSpace.exp (-Y0)‖ ≤ _
    exact hraw.trans
      (mul_le_mul_of_nonneg_left hneg
        (cmp102ExpLipschitzBudget_nonneg R
          (cmp102SourceLogAverageRadius_nonneg hr0)))
  have hCdiff : ‖Matrix.conjTranspose CU - Matrix.conjTranspose C0‖ ≤
      (M : ℝ) * ε := by
    calc
      ‖Matrix.conjTranspose CU - Matrix.conjTranspose C0‖ =
          ‖Matrix.conjTranspose (CU - C0)‖ := by
        rw [Matrix.conjTranspose_sub]
      _ = ‖CU - C0‖ := Matrix.l2_opNorm_conjTranspose (CU - C0)
      _ ≤ (M : ℝ) * ε :=
        norm_cmp98SourceCoarseContour_zero_sub_trivial_le
          U ε hε hsmall A b
  have hC0 : ‖Matrix.conjTranspose C0‖ = 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact norm_cmp98ContourMatrixCurve_eq_one U0 A _ 0
  have halg :
      Matrix.conjTranspose CU * EU - Matrix.conjTranspose C0 * E0 =
        (Matrix.conjTranspose CU - Matrix.conjTranspose C0) * EU +
          Matrix.conjTranspose C0 * (EU - E0) := by
    noncomm_ring
  unfold cmp98Eq119NonlinearBlockInverseAtZero
  change ‖Matrix.conjTranspose CU * EU -
      Matrix.conjTranspose C0 * E0‖ ≤ _
  rw [halg]
  calc
    ‖(Matrix.conjTranspose CU - Matrix.conjTranspose C0) * EU +
        Matrix.conjTranspose C0 * (EU - E0)‖
        ≤ ‖Matrix.conjTranspose CU - Matrix.conjTranspose C0‖ * ‖EU‖ +
            ‖Matrix.conjTranspose C0‖ * ‖EU - E0‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ ((M : ℝ) * ε) * O +
          1 * cmp102PhysicalExpAverageBackgroundValueBudget d M r ε := by
      apply add_le_add
      · exact mul_le_mul hCdiff hEU (norm_nonneg EU)
          (mul_nonneg (Nat.cast_nonneg M) hε)
      · exact mul_le_mul (le_of_eq hC0) hEdiff (norm_nonneg _)
          (by norm_num)
    _ = cmp102PhysicalRightInverseBackgroundBudget d M r ε := by
      unfold cmp102PhysicalRightInverseBackgroundBudget O
      ring

end

end YangMills.RG
