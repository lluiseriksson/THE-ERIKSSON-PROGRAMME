/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4FullComplexGamma
import YangMills.RG.BalabanCMP116SourcePi4FullComplexR2PhysicalBound

/-!
# Bilateral physical norm of the source-complex `R3`

The exact source identity

`R3 = -C_elimᵀ R2 (C_elim P_(Z0ᶜ)) root`

is combined with the physical row and column bounds for `R2`.  The resulting
budgets contain only literal source matrices and explicit contour constants;
no generic Gamma-defect norm is supplied.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private theorem linfty_opNorm_mul_four_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A B C D : Matrix ι ι ℂ) :
    ‖A * B * C * D‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ := by
  calc
    ‖A * B * C * D‖ ≤ ‖A * B * C‖ * ‖D‖ :=
      Matrix.linfty_opNorm_mul _ _
    _ ≤ (‖A * B‖ * ‖C‖) * ‖D‖ :=
      mul_le_mul_of_nonneg_right
        (Matrix.linfty_opNorm_mul _ _) (norm_nonneg D)
    _ ≤ (‖A‖ * ‖B‖ * ‖C‖) * ‖D‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (Matrix.linfty_opNorm_mul A B) (norm_nonneg C))
        (norm_nonneg D)

private theorem linfty_opNorm_transpose_mul_four_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A B C D : Matrix ι ι ℂ) :
    ‖(A * B * C * D).transpose‖ ≤
      ‖D.transpose‖ * ‖C.transpose‖ * ‖B.transpose‖ *
        ‖A.transpose‖ := by
  simpa only [Matrix.transpose_mul, Matrix.mul_assoc, mul_assoc] using
    (linfty_opNorm_mul_four_le D.transpose C.transpose B.transpose A.transpose)

/-- Explicit row budget of the literal source `R3`. -/
noncomputable def cmp116SourcePi4PhysicalComplexR3RowBound
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (K root : PhysicalEndomorphism M Q Nc)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (Delta : ℕ) (Ahead rho rate radius Rweak : ℝ) : ℝ :=
  ‖(cmp116SourcePi4ConstraintMatrix M Q Nc).transpose‖ *
    cmp116SourcePi4PhysicalComplexR2RowBound
      K Delta Ahead rho rate radius Rweak *
    ‖cmp116SourcePi4ConstraintMatrix M Q Nc *
      cmp116SourcePi4ComplementProjectionMatrix
        (M := M) (Nc := Nc) Z0‖ *
    ‖cmp116SourcePi4ReferenceRootMatrix root‖

/-- Explicit column budget of the literal source `R3`. -/
noncomputable def cmp116SourcePi4PhysicalComplexR3ColumnBound
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (K root : PhysicalEndomorphism M Q Nc)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (Delta : ℕ) (Ahead rho rate radius Rweak : ℝ) : ℝ :=
  ‖(cmp116SourcePi4ReferenceRootMatrix root).transpose‖ *
    ‖(cmp116SourcePi4ConstraintMatrix M Q Nc *
      cmp116SourcePi4ComplementProjectionMatrix
        (M := M) (Nc := Nc) Z0).transpose‖ *
    cmp116SourcePi4PhysicalComplexR2ColumnBound
      K Delta Ahead rho rate radius Rweak *
    ‖cmp116SourcePi4ConstraintMatrix M Q Nc‖

/-- Pure matrix consequence of the literal source identity: a row estimate
for `R2` propagates through the exact Gamma correction. -/
theorem linfty_opNorm_cmp116SourcePi4FullComplexR3Matrix_le_of_R2
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K root : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (sigma : FinBox 4 (2 * Q) → ℂ)
    {r2Bound : ℝ}
    (hR2 :
      ‖cmp116SourcePi4FullComplexR2Matrix
        (R := R) anchor K hc hmass hK sigma‖ ≤ r2Bound) :
    ‖cmp116SourcePi4FullComplexR3Matrix
        (R := R) anchor K root hc hmass hK Z0 sigma‖ ≤
      ‖(cmp116SourcePi4ConstraintMatrix M Q Nc).transpose‖ *
        r2Bound *
        ‖cmp116SourcePi4ConstraintMatrix M Q Nc *
          cmp116SourcePi4ComplementProjectionMatrix
            (M := M) (Nc := Nc) Z0‖ *
        ‖cmp116SourcePi4ReferenceRootMatrix root‖ := by
  rw [cmp116SourcePi4FullComplexR3Matrix_eq_neg_constraint_mul_R2,
    norm_neg]
  calc
    ‖(cmp116SourcePi4ConstraintMatrix M Q Nc).transpose *
          cmp116SourcePi4FullComplexR2Matrix
            (R := R) anchor K hc hmass hK sigma *
          (cmp116SourcePi4ConstraintMatrix M Q Nc *
            cmp116SourcePi4ComplementProjectionMatrix
              (M := M) (Nc := Nc) Z0) *
          cmp116SourcePi4ReferenceRootMatrix root‖ ≤
        ‖(cmp116SourcePi4ConstraintMatrix M Q Nc).transpose *
          cmp116SourcePi4FullComplexR2Matrix
            (R := R) anchor K hc hmass hK sigma *
          (cmp116SourcePi4ConstraintMatrix M Q Nc *
            cmp116SourcePi4ComplementProjectionMatrix
              (M := M) (Nc := Nc) Z0)‖ *
          ‖cmp116SourcePi4ReferenceRootMatrix root‖ :=
      Matrix.linfty_opNorm_mul _ _
    _ ≤
        (‖(cmp116SourcePi4ConstraintMatrix M Q Nc).transpose *
          cmp116SourcePi4FullComplexR2Matrix
            (R := R) anchor K hc hmass hK sigma‖ *
          ‖cmp116SourcePi4ConstraintMatrix M Q Nc *
            cmp116SourcePi4ComplementProjectionMatrix
              (M := M) (Nc := Nc) Z0‖) *
          ‖cmp116SourcePi4ReferenceRootMatrix root‖ := by
      gcongr
      exact Matrix.linfty_opNorm_mul _ _
    _ ≤
        ((‖(cmp116SourcePi4ConstraintMatrix M Q Nc).transpose‖ *
          r2Bound) *
          ‖cmp116SourcePi4ConstraintMatrix M Q Nc *
            cmp116SourcePi4ComplementProjectionMatrix
              (M := M) (Nc := Nc) Z0‖) *
          ‖cmp116SourcePi4ReferenceRootMatrix root‖ := by
      gcongr
      exact
        (Matrix.linfty_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_left hR2 (norm_nonneg _))
    _ = _ := by ring

/-- Column companion of the preceding exact factor estimate. -/
theorem linfty_opNorm_transpose_cmp116SourcePi4FullComplexR3Matrix_le_of_R2
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K root : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (sigma : FinBox 4 (2 * Q) → ℂ)
    {r2ColumnBound : ℝ}
    (hR2 :
      ‖(cmp116SourcePi4FullComplexR2Matrix
        (R := R) anchor K hc hmass hK sigma).transpose‖ ≤
          r2ColumnBound) :
    ‖(cmp116SourcePi4FullComplexR3Matrix
        (R := R) anchor K root hc hmass hK Z0 sigma).transpose‖ ≤
      ‖(cmp116SourcePi4ReferenceRootMatrix root).transpose‖ *
        ‖(cmp116SourcePi4ConstraintMatrix M Q Nc *
          cmp116SourcePi4ComplementProjectionMatrix
            (M := M) (Nc := Nc) Z0).transpose‖ *
        r2ColumnBound *
        ‖cmp116SourcePi4ConstraintMatrix M Q Nc‖ := by
  rw [cmp116SourcePi4FullComplexR3Matrix_eq_neg_constraint_mul_R2]
  rw [Matrix.transpose_neg, norm_neg]
  calc
    ‖((cmp116SourcePi4ConstraintMatrix M Q Nc).transpose *
        cmp116SourcePi4FullComplexR2Matrix
          (R := R) anchor K hc hmass hK sigma *
        (cmp116SourcePi4ConstraintMatrix M Q Nc *
          cmp116SourcePi4ComplementProjectionMatrix
            (M := M) (Nc := Nc) Z0) *
        cmp116SourcePi4ReferenceRootMatrix root).transpose‖ ≤
      ((‖(cmp116SourcePi4ReferenceRootMatrix root).transpose‖ *
        ‖(cmp116SourcePi4ConstraintMatrix M Q Nc *
          cmp116SourcePi4ComplementProjectionMatrix
            (M := M) (Nc := Nc) Z0).transpose‖) *
        ‖(cmp116SourcePi4FullComplexR2Matrix
          (R := R) anchor K hc hmass hK sigma).transpose‖) *
        ‖cmp116SourcePi4ConstraintMatrix M Q Nc‖ := by
      simpa only [Matrix.transpose_transpose] using
        (linfty_opNorm_transpose_mul_four_le
          (cmp116SourcePi4ConstraintMatrix M Q Nc).transpose
          (cmp116SourcePi4FullComplexR2Matrix
            (R := R) anchor K hc hmass hK sigma)
          (cmp116SourcePi4ConstraintMatrix M Q Nc *
            cmp116SourcePi4ComplementProjectionMatrix
              (M := M) (Nc := Nc) Z0)
          (cmp116SourcePi4ReferenceRootMatrix root))
    _ ≤
      ((‖(cmp116SourcePi4ReferenceRootMatrix root).transpose‖ *
        ‖(cmp116SourcePi4ConstraintMatrix M Q Nc *
          cmp116SourcePi4ComplementProjectionMatrix
            (M := M) (Nc := Nc) Z0).transpose‖) *
        r2ColumnBound) *
        ‖cmp116SourcePi4ConstraintMatrix M Q Nc‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hR2
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
        (norm_nonneg _)
    _ = _ := by ring

end

end YangMills.RG
