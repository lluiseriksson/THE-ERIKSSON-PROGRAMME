/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102PhysicalCorrectionField
import YangMills.RG.BalabanCMP116AdjointSmallBridge
import YangMills.RG.BalabanCMP116MatrixTraceL2OpNorm

/-!
# Norm transport for the physical CMP102 correction

CMP98 controls the L2 operator norm of the decoded matrix remainder, whereas
the physical cochain stores orthonormal `su(N)` coordinates.  These norms are
not equal.  This module records an explicit finite-dimensional comparison:
the Frobenius/coordinate norm costs at most a factor `Nc` relative to the
matrix operator norm.

The factor is intentionally visible.  It is enough to turn the pointwise
CMP98 estimate into a volume-independent sup-norm estimate for the assembled
correction field.  No L2 norm over all lattice bonds is introduced.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- The packaged Frobenius norm costs at most the matrix dimension relative
to the L2 operator norm. -/
theorem norm_matrixFrobEuclid_le_card_mul_l2_opNorm
    (A : Matrix (Fin Nc) (Fin Nc) ℂ) :
    ‖matrixFrobEuclid A‖ ≤ (Nc : ℝ) * ‖A‖ := by
  have hsq :
      ‖matrixFrobEuclid A‖ ^ 2 ≤ ((Nc : ℝ) * ‖A‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    change
      (∑ p : Fin Nc × Fin Nc, ‖A p.1 p.2‖ ^ 2) ≤
        ((Nc : ℝ) * ‖A‖) ^ 2
    calc
      (∑ p : Fin Nc × Fin Nc, ‖A p.1 p.2‖ ^ 2)
          ≤ ∑ _p : Fin Nc × Fin Nc, ‖A‖ ^ 2 := by
            apply Finset.sum_le_sum
            intro p hp
            exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
              (norm_matrix_entry_le_l2_opNorm A p.1 p.2)
      _ = ((Nc : ℝ) * ‖A‖) ^ 2 := by
        simp [pow_two]
        ring
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))).mp hsq

/-- Canonical `su(N)` coordinates cost at most `Nc` relative to the decoded
matrix L2 operator norm. -/
theorem norm_lieCoord_le_card_mul_norm_toMatrix
    (X : SUNLieCoord Nc) :
    ‖X‖ ≤ (Nc : ℝ) * ‖cmp98LieCoordToAmbientCLM Nc X‖ := by
  rw [← (suLieCoordIso Nc).symm.norm_map X,
    norm_suLie_eq_norm_matrixFrobEuclid,
    cmp98LieCoordToAmbientCLM_apply]
  exact norm_matrixFrobEuclid_le_card_mul_l2_opNorm
    (((suLieCoordIso Nc).symm X).toMatrix)

/-- The source-explicit scalar budget for the unit-endpoint correction. -/
def cmp102PhysicalCorrectionSourceBudget
    (A : PhysicalGaugeOneCochain d (M * N') Nc) (r : ℝ) : ℝ :=
  let R := cmp98SourceLogAverageRadius r
  let D := nearLogDerivativeBudget r *
    cmp98SourceContourDisplacementBudget A 1
  let Q := nearLogSecondDerivativeBudget r *
        cmp98SourceContourDisplacementBudget A 1 ^ 2 +
      nearLogDerivativeBudget r *
        cmp98SourceContourQuadraticBudget A 1
  let QE := expSecondDerivativeBudget R * D ^ 2 +
    expDerivativeBudget R * Q
  let B := cmp98SourcePhysicalBlockDisplacementBudget A 1 r
  B ^ 2 / (1 - B) +
    (QE + cmp98SourceOuterExpNormBudget r *
        cmp98SourceCoarseContourQuadraticBudget A 1 +
      cmp98SourceOuterExpDisplacementBudget A 1 r *
        cmp98SourceCoarseContourDisplacementBudget A 1) *
      cmp98SourceOuterExpNormBudget r

/-- The finite, volume-independent sup norm of the physical correction
field. -/
def cmp102PhysicalCorrectionSupNorm
    (C : CoarsePhysicalOneCochain d N' Nc) : ℝ :=
  (Finset.univ.image fun b : PhysicalBond d N' => ‖C b‖).max'
    (by simp)

/- Every correction coordinate is bounded by its field sup norm. -/
omit [NeZero Nc] in
theorem norm_apply_le_cmp102PhysicalCorrectionSupNorm
    (C : CoarsePhysicalOneCochain d N' Nc)
    (b : PhysicalBond d N') :
    ‖C b‖ ≤ cmp102PhysicalCorrectionSupNorm C := by
  unfold cmp102PhysicalCorrectionSupNorm
  exact Finset.le_max' _ _ (by simp)

set_option maxHeartbeats 3000000 in
/-- Volume-uniform source bound for the assembled physical correction field.
The only dimension loss is the explicit color factor `Nc`. -/
theorem cmp102PhysicalCorrectionSupNorm_le_sourceBudget
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (Chart : CMP102PhysicalNonlinearFieldChart U A)
    (r : ℝ)
    (hbase : ∀ b : PhysicalBond d N', ∀ x ∈ blockOf M N' b.1,
      ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ 1 / 3)
    (hsmall : cmp98SourceFieldSupNorm A ≤ 1 / 2)
    (hr : 1 / 3 + cmp98SourceContourDisplacementBudget A 1 ≤ r)
    (hr1 : r < 1)
    (hdev1 : cmp98SourcePhysicalBlockDisplacementBudget A 1 r < 1) :
    cmp102PhysicalCorrectionSupNorm
        (cmp102PhysicalNonlinearCorrectionField U A Chart) ≤
      (Nc : ℝ) * cmp102PhysicalCorrectionSourceBudget A r := by
  unfold cmp102PhysicalCorrectionSupNorm
  apply Finset.max'_le
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
  calc
    ‖cmp102PhysicalNonlinearCorrectionField U A Chart b‖
        ≤ (Nc : ℝ) *
          ‖cmp98LieCoordToAmbientCLM Nc
            (cmp102PhysicalNonlinearCorrectionField U A Chart b)‖ :=
      norm_lieCoord_le_card_mul_norm_toMatrix _
    _ ≤ (Nc : ℝ) * cmp102PhysicalCorrectionSourceBudget A r := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg Nc)
      simpa only [cmp102PhysicalCorrectionSourceBudget] using
        norm_cmp102PhysicalNonlinearCorrectionField_toMatrix_le_sourceBudget
          U A Chart b r (hbase b) hsmall hr hr1 hdev1

end

end YangMills.RG
