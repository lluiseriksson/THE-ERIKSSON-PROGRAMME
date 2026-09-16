/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116MatrixTraceNearLog
import YangMills.RG.BalabanCMP116SourcePi4FullComplexContourDefect
import YangMills.RG.BalabanCMP116SourcePi4FullComplexContourNonsingularity
import YangMills.RG.BalabanCMP116SourceRestrictedCoordinatePivotMatrixLayer

/-!
# Passing a restricted physical defect layer expansion through trace

The complete covariance difference is exposed as the norm-convergent sum of
its length layers.  An arbitrary traced two-sided multiplication is a
continuous real-linear functional, so it may be passed through that sum
without any double-series rearrangement.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Whenever the physical difference layers and the base layers are
summable, their `tsum` is literally the complete covariance difference. -/
theorem cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_sub_one_eq_tsum_layers
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hdiff : Summable fun layer : ℕ =>
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK sigma layer -
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK (fun _ => 1) layer)
    (hone : Summable fun layer : ℕ =>
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer
        (R := R) anchor K hc hmass hK (fun _ => 1) layer) :
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK sigma -
        cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK (fun _ => 1) =
      ∑' layer : ℕ,
        (cmp116SourcePi4FullComplexWeakenedCovarianceLayer
            (R := R) anchor K hc hmass hK sigma layer -
          cmp116SourcePi4FullComplexWeakenedCovarianceLayer
            (R := R) anchor K hc hmass hK (fun _ => 1) layer) := by
  let sigmaLayer := fun layer : ℕ =>
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer
      (R := R) anchor K hc hmass hK sigma layer
  let oneLayer := fun layer : ℕ =>
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer
      (R := R) anchor K hc hmass hK (fun _ => 1) layer
  have hdiff' : Summable fun layer : ℕ =>
      sigmaLayer layer - oneLayer layer := hdiff
  have hone' : Summable oneLayer := hone
  have hsigma : Summable sigmaLayer := by
    have hadd := hdiff'.add hone'
    exact hadd.congr fun layer => by
      exact sub_add_cancel (sigmaLayer layer) (oneLayer layer)
  have hsigmaMatrix :
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK sigma =
        ∑' layer : ℕ, sigmaLayer layer := by
    funext row col
    rw [cmp116SourcePi4FullComplexWeakenedCovarianceMatrix]
    symm
    calc
      (∑' layer : ℕ, sigmaLayer layer) row col =
          (∑' layer : ℕ, sigmaLayer layer row) col := by
        exact congrFun (tsum_apply (x := row) hsigma) col
      _ = ∑' layer : ℕ, sigmaLayer layer row col :=
        tsum_apply ((Pi.summable.mp hsigma) row)
  have honeMatrix :
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK (fun _ => 1) =
        ∑' layer : ℕ, oneLayer layer := by
    funext row col
    rw [cmp116SourcePi4FullComplexWeakenedCovarianceMatrix]
    symm
    calc
      (∑' layer : ℕ, oneLayer layer) row col =
          (∑' layer : ℕ, oneLayer layer row) col := by
        exact congrFun (tsum_apply (x := row) hone') col
      _ = ∑' layer : ℕ, oneLayer layer row col :=
        tsum_apply ((Pi.summable.mp hone') row)
  rw [hsigmaMatrix, honeMatrix]
  simpa only [sigmaLayer, oneLayer] using
    (hsigma.tsum_sub hone').symm

/-- Traced two-sided multiplication passes through the physical length-layer
sum by continuity. -/
theorem cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_sub_one_trace_mul_pow_eq_tsum_layers
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hdiff : Summable fun layer : ℕ =>
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK sigma layer -
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK (fun _ => 1) layer)
    (hone : Summable fun layer : ℕ =>
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer
        (R := R) anchor K hc hmass hK (fun _ => 1) layer)
    (P D : Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ)
    (m : ℕ) :
    Matrix.trace
        ((P *
          (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
              (R := R) anchor K hc hmass hK sigma -
            cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
              (R := R) anchor K hc hmass hK (fun _ => 1))) * D ^ m) =
      ∑' layer : ℕ,
        Matrix.trace
          ((P *
            (cmp116SourcePi4FullComplexWeakenedCovarianceLayer
                (R := R) anchor K hc hmass hK sigma layer -
              cmp116SourcePi4FullComplexWeakenedCovarianceLayer
                (R := R) anchor K hc hmass hK (fun _ => 1) layer)) *
            D ^ m) := by
  let L0 :
      Matrix
          (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
          (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ →ₗ[ℝ] ℂ := {
    toFun := fun A => Matrix.trace ((P * A) * D ^ m)
    map_add' := by
      intro A B
      simp [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
    map_smul' := by
      intro r A
      simp [Matrix.trace_smul]
  }
  let L :
      Matrix
          (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
          (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ →L[ℝ] ℂ :=
    L0.mkContinuous
      ((Fintype.card
          (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) : ℝ) *
        (‖P‖ * ‖D ^ m‖)) (by
          intro A
          calc
            ‖Matrix.trace ((P * A) * D ^ m)‖ ≤
                (Fintype.card
                    (CMP116PhysicalWalkCoordinate
                      4 (M * (2 * Q)) Nc) : ℝ) *
                  ‖(P * A) * D ^ m‖ :=
              norm_matrix_trace_le_card_mul_linfty_opNorm _
            _ ≤
                (Fintype.card
                    (CMP116PhysicalWalkCoordinate
                      4 (M * (2 * Q)) Nc) : ℝ) *
                  ((‖P‖ * ‖A‖) * ‖D ^ m‖) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              calc
                ‖(P * A) * D ^ m‖ ≤ ‖P * A‖ * ‖D ^ m‖ :=
                  Matrix.linfty_opNorm_mul _ _
                _ ≤ (‖P‖ * ‖A‖) * ‖D ^ m‖ := by
                  gcongr
                  exact Matrix.linfty_opNorm_mul _ _
            _ =
                ((Fintype.card
                    (CMP116PhysicalWalkCoordinate
                      4 (M * (2 * Q)) Nc) : ℝ) *
                  (‖P‖ * ‖D ^ m‖)) * ‖A‖ := by ring)
  have hmap := L.map_tsum hdiff
  rw [
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_sub_one_eq_tsum_layers
      anchor K hc hmass hK sigma hdiff hone]
  exact hmap

/-- The positive trace powers of the literal relative covariance defect are
exactly the traced length-layer sum obtained by expanding only their first
defect factor. -/
theorem trace_cmp116SourcePi4FullComplexRelativeCovarianceDefect_pow_succ_eq_tsum_layers
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hdiff : Summable fun layer : ℕ =>
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK sigma layer -
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK (fun _ => 1) layer)
    (hone : Summable fun layer : ℕ =>
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer
        (R := R) anchor K hc hmass hK (fun _ => 1) layer)
    (m : ℕ) :
    Matrix.trace
        ((cmp116SourcePi4FullComplexRelativeCovarianceDefect
          (R := R) anchor K hc hmass hK sigma) ^ (m + 1)) =
      ∑' layer : ℕ,
        Matrix.trace
          ((cmp116PhysicalEndomorphismComplexMatrix K *
            (cmp116SourcePi4FullComplexWeakenedCovarianceLayer
                (R := R) anchor K hc hmass hK sigma layer -
              cmp116SourcePi4FullComplexWeakenedCovarianceLayer
                (R := R) anchor K hc hmass hK (fun _ => 1) layer)) *
            (cmp116SourcePi4FullComplexRelativeCovarianceDefect
              (R := R) anchor K hc hmass hK sigma) ^ m) := by
  let D :=
    cmp116SourcePi4FullComplexRelativeCovarianceDefect
      (R := R) anchor K hc hmass hK sigma
  calc
    Matrix.trace (D ^ (m + 1)) =
        Matrix.trace (D * D ^ m) := by
      exact congrArg Matrix.trace (pow_succ' D m)
    _ = ∑' layer : ℕ,
        Matrix.trace
          ((cmp116PhysicalEndomorphismComplexMatrix K *
            (cmp116SourcePi4FullComplexWeakenedCovarianceLayer
                (R := R) anchor K hc hmass hK sigma layer -
              cmp116SourcePi4FullComplexWeakenedCovarianceLayer
                (R := R) anchor K hc hmass hK (fun _ => 1) layer)) *
            D ^ m) := by
      dsimp [D]
      unfold cmp116SourcePi4FullComplexRelativeCovarianceDefect
      exact
        cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_sub_one_trace_mul_pow_eq_tsum_layers
          anchor K hc hmass hK sigma hdiff hone
          (cmp116PhysicalEndomorphismComplexMatrix K)
          (cmp116PhysicalEndomorphismComplexMatrix K *
            (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
                (R := R) anchor K hc hmass hK sigma -
              cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
                (R := R) anchor K hc hmass hK (fun _ => 1)))
          m

end

end YangMills.RG
