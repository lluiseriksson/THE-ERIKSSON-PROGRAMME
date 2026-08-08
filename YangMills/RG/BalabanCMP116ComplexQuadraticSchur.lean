/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ActiveDeterminantBound
import YangMills.RG.BalabanCMP116Eq214PhysicalContourRealPart

/-!
# Bilateral Schur control of the CMP116 complex quadratic form

The analytic contour quadratic uses transpose, not conjugate transpose.  A
row bound alone is therefore insufficient for its `L²` quadratic form.  This
module keeps both Schur directions visible: rows are controlled by the
matrix `L∞` norm of `A`, and columns by the same norm of `A.transpose`.

The resulting coefficient contains no cardinality of the ambient coordinate
space.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators
open scoped Matrix.Norms.Operator

noncomputable section

/-- Bilateral Schur estimate for the real part of the analytic CMP116
quadratic form.  The factor `1 / 4` includes both the `1 / 2` in the
definition of `cmp116Eq214ComplexQuadratic` and the elementary inequality
`2 |xᵢ| |xⱼ| ≤ xᵢ² + xⱼ²`. -/
theorem cmp116Eq214ComplexQuadratic_re_le_linfty_bilateral
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) (x : ι → ℝ) :
    (cmp116Eq214ComplexQuadratic A x).re ≤
      (‖A‖ + ‖A.transpose‖) / 4 * ∑ i, x i ^ 2 := by
  rw [cmp116Eq214ComplexQuadratic_re]
  simp only [dotProduct, Matrix.mulVec, cmp116Eq214RealPartMatrix]
  calc
    (1 / 2 : ℝ) * ∑ i, x i * ∑ j, (A i j).re * x j
        = (1 / 2 : ℝ) * ∑ i, ∑ j, x i * (A i j).re * x j := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ 
        ≤ (1 / 2 : ℝ) *
            ∑ i, ∑ j, |x i| * ‖A i j‖ * |x j| := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          calc
            x i * (A i j).re * x j
                ≤ |x i * (A i j).re * x j| := le_abs_self _
            _ = |x i| * |(A i j).re| * |x j| := by
              rw [abs_mul, abs_mul]
            _ ≤ |x i| * ‖A i j‖ * |x j| := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left
                  (Complex.abs_re_le_norm _) (abs_nonneg _))
                (abs_nonneg _)
    _ ≤ (1 / 4 : ℝ) *
          ∑ i, ∑ j, ‖A i j‖ * (x i ^ 2 + x j ^ 2) := by
      rw [show (1 / 4 : ℝ) = (1 / 2) * (1 / 2) by norm_num,
        mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc
        (∑ i, ∑ j, |x i| * ‖A i j‖ * |x j|)
            ≤ ∑ i, ∑ j,
                (1 / 2 : ℝ) * (‖A i j‖ * (x i ^ 2 + x j ^ 2)) := by
              apply Finset.sum_le_sum
              intro i _
              apply Finset.sum_le_sum
              intro j _
              have hxy := two_mul_le_add_sq (|x i|) (|x j|)
              calc
                |x i| * ‖A i j‖ * |x j|
                    = ‖A i j‖ / 2 * (2 * |x i| * |x j|) := by ring
                _ ≤ ‖A i j‖ / 2 * (|x i| ^ 2 + |x j| ^ 2) := by
                  exact mul_le_mul_of_nonneg_left hxy
                    (div_nonneg (norm_nonneg _) (by norm_num))
                _ = (1 / 2 : ℝ) *
                    (‖A i j‖ * (x i ^ 2 + x j ^ 2)) := by
                  rw [sq_abs, sq_abs]
                  ring
        _ = (1 / 2 : ℝ) *
              ∑ i, ∑ j, ‖A i j‖ * (x i ^ 2 + x j ^ 2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
    _ = (1 / 4 : ℝ) *
          ((∑ i, x i ^ 2 * ∑ j, ‖A i j‖) +
            ∑ j, x j ^ 2 * ∑ i, ‖A i j‖) := by
      have hsplit :
          (∑ i, ∑ j, ‖A i j‖ * (x i ^ 2 + x j ^ 2)) =
            (∑ i, ∑ j, ‖A i j‖ * x i ^ 2) +
              ∑ i, ∑ j, ‖A i j‖ * x j ^ 2 := by
        simp only [mul_add, Finset.sum_add_distrib]
      have hfirst :
          (∑ i, ∑ j, ‖A i j‖ * x i ^ 2) =
            ∑ i, x i ^ 2 * ∑ j, ‖A i j‖ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hsecond :
          (∑ i, ∑ j, ‖A i j‖ * x j ^ 2) =
            ∑ j, x j ^ 2 * ∑ i, ‖A i j‖ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hsplit, hfirst, hsecond]
    _ ≤ (1 / 4 : ℝ) *
          ((∑ i, x i ^ 2 * ‖A‖) +
            ∑ j, x j ^ 2 * ‖A.transpose‖) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply add_le_add
      · apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left
          (Matrix.row_sum_norm_le_linfty_opNorm A i) (sq_nonneg _)
      · apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        simpa [Matrix.transpose_apply] using
          (Matrix.row_sum_norm_le_linfty_opNorm A.transpose j)
    _ = (‖A‖ + ‖A.transpose‖) / 4 * ∑ i, x i ^ 2 := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      ring

namespace Matrix

/-- Three-factor submultiplicativity for the matrix `L∞` operator norm. -/
theorem linfty_opNorm_mul_three_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A B C : Matrix ι ι ℂ) :
    ‖A * B * C‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ := by
  calc
    ‖A * B * C‖ ≤ ‖A * B‖ * ‖C‖ := Matrix.linfty_opNorm_mul _ _
    _ ≤ (‖A‖ * ‖B‖) * ‖C‖ := by
      exact mul_le_mul_of_nonneg_right
        (Matrix.linfty_opNorm_mul A B) (norm_nonneg C)

/-- The column-direction counterpart of `linfty_opNorm_mul_three_le`,
expressed as a row norm after analytic transpose. -/
theorem linfty_opNorm_transpose_mul_three_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A B C : Matrix ι ι ℂ) :
    ‖(A * B * C).transpose‖ ≤
      ‖C.transpose‖ * ‖B.transpose‖ * ‖A.transpose‖ := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.mul_assoc]
  exact Matrix.linfty_opNorm_mul_three_le C.transpose B.transpose A.transpose

end Matrix

/-- Explicit bilateral Schur budget of the exact three-term `R₁` telescope.
Every summand contains either the source defect `G1-G0` or the covariance
defect `C1-C0`; hence the budget retains contour smallness instead of
bounding the two full sandwiches separately. -/
noncomputable def cmp116R1TelescopeBilateralSchurBudget
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (G0 G1 C0 C1 : Matrix ι ι ℂ) : ℝ :=
  let R3 := G1 - G0
  let Cdiff := C1 - C0
  let rowBudget :=
    ‖R3.transpose‖ * ‖C1‖ * ‖G1‖ +
      ‖G0.transpose‖ * ‖Cdiff‖ * ‖G1‖ +
      ‖G0.transpose‖ * ‖C0‖ * ‖R3‖
  let columnBudget :=
    ‖G1.transpose‖ * ‖C1.transpose‖ * ‖R3‖ +
      ‖G1.transpose‖ * ‖Cdiff.transpose‖ * ‖G0‖ +
      ‖R3.transpose‖ * ‖C0.transpose‖ * ‖G0‖
  (rowBudget + columnBudget) / 4

/-- The exact bilateral rate of a covariance-sandwich correction is bounded
by its small-defect telescope budget.  This is the algebraic bridge needed
before inserting volume-uniform physical row and column estimates. -/
theorem cmp116R1BilateralSchurRate_le_telescopeBudget
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (G0 G1 C0 C1 : Matrix ι ι ℂ) :
    let R1 :=
      Matrix.transpose G1 * C1 * G1 -
        Matrix.transpose G0 * C0 * G0
    (‖R1‖ + ‖R1.transpose‖) / 4 ≤
      cmp116R1TelescopeBilateralSchurBudget G0 G1 C0 C1 := by
  dsimp only
  let R3 := G1 - G0
  let Cdiff := C1 - C0
  let T1 := Matrix.transpose R3 * C1 * G1
  let T2 := Matrix.transpose G0 * Cdiff * G1
  let T3 := Matrix.transpose G0 * C0 * R3
  have htelescope :
      Matrix.transpose G1 * C1 * G1 -
          Matrix.transpose G0 * C0 * G0 =
        T1 + T2 + T3 := by
    simpa [R3, Cdiff, T1, T2, T3] using
      (Matrix.transpose_mul_cov_mul_sub_eq_telescope G0 G1 C0 C1)
  have hrow :
      ‖Matrix.transpose G1 * C1 * G1 -
          Matrix.transpose G0 * C0 * G0‖ ≤
        ‖R3.transpose‖ * ‖C1‖ * ‖G1‖ +
          ‖G0.transpose‖ * ‖Cdiff‖ * ‖G1‖ +
          ‖G0.transpose‖ * ‖C0‖ * ‖R3‖ := by
    rw [htelescope]
    calc
      ‖T1 + T2 + T3‖ ≤ ‖T1 + T2‖ + ‖T3‖ := norm_add_le _ _
      _ ≤ (‖T1‖ + ‖T2‖) + ‖T3‖ := by
        exact add_le_add (norm_add_le T1 T2) le_rfl
      _ ≤
          (‖R3.transpose‖ * ‖C1‖ * ‖G1‖ +
              ‖G0.transpose‖ * ‖Cdiff‖ * ‖G1‖) +
            ‖G0.transpose‖ * ‖C0‖ * ‖R3‖ := by
        exact add_le_add
          (add_le_add
            (Matrix.linfty_opNorm_mul_three_le R3.transpose C1 G1)
            (Matrix.linfty_opNorm_mul_three_le G0.transpose Cdiff G1))
          (Matrix.linfty_opNorm_mul_three_le G0.transpose C0 R3)
  have hcolumn :
      ‖(Matrix.transpose G1 * C1 * G1 -
          Matrix.transpose G0 * C0 * G0).transpose‖ ≤
        ‖G1.transpose‖ * ‖C1.transpose‖ * ‖R3‖ +
          ‖G1.transpose‖ * ‖Cdiff.transpose‖ * ‖G0‖ +
          ‖R3.transpose‖ * ‖C0.transpose‖ * ‖G0‖ := by
    rw [htelescope, Matrix.transpose_add, Matrix.transpose_add]
    calc
      ‖T1.transpose + T2.transpose + T3.transpose‖ ≤
          ‖T1.transpose + T2.transpose‖ + ‖T3.transpose‖ :=
        norm_add_le _ _
      _ ≤ (‖T1.transpose‖ + ‖T2.transpose‖) + ‖T3.transpose‖ := by
        exact add_le_add (norm_add_le T1.transpose T2.transpose) le_rfl
      _ ≤
          (‖G1.transpose‖ * ‖C1.transpose‖ * ‖R3‖ +
              ‖G1.transpose‖ * ‖Cdiff.transpose‖ * ‖G0‖) +
            ‖R3.transpose‖ * ‖C0.transpose‖ * ‖G0‖ := by
        exact add_le_add
          (add_le_add
            (Matrix.linfty_opNorm_transpose_mul_three_le R3.transpose C1 G1)
            (Matrix.linfty_opNorm_transpose_mul_three_le G0.transpose Cdiff G1))
          (Matrix.linfty_opNorm_transpose_mul_three_le G0.transpose C0 R3)
  unfold cmp116R1TelescopeBilateralSchurBudget
  dsimp only
  exact div_le_div_of_nonneg_right (add_le_add hrow hcolumn) (by norm_num)

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- The exact bilateral Schur rate of the literal source-complex `R₁`.
Unlike an arbitrary `outerRate`, this is generated from the physical matrix
itself.  A later source estimate must still prove that this concrete rate is
uniform and carrier-local; this definition does not hide that obligation. -/
noncomputable def cmp116SourcePi4FullComplexR1BilateralSchurRate
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K root : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (sigma : FinBox 4 (2 * Q) → ℂ) : ℝ :=
  let R1 :=
    cmp116SourcePi4FullComplexR1Matrix
      (R := R) anchor K root hc hmass hK Z0 sigma
  (‖R1‖ + ‖R1.transpose‖) / 4

/-- Source-specific small-defect telescope budget for the literal complex
`R₁`.  The four matrices are not caller-supplied: they are the full complex
Gamma/covariance and their fully coupled physical reference values. -/
noncomputable def cmp116SourcePi4FullComplexR1TelescopeSchurBudget
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K root : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (sigma : FinBox 4 (2 * Q) → ℂ) : ℝ :=
  cmp116R1TelescopeBilateralSchurBudget
    (cmp116SourcePi4PhysicalBaseGammaMatrix K root Z0)
    (cmp116SourcePi4FullComplexGammaMatrix
      (R := R) anchor K root hc hmass hK Z0 sigma)
    (cmp116SourcePi4PhysicalBaseCovarianceMatrix K hc hmass hK)
    (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK sigma)

/-- The generated bilateral rate of the literal complex `R₁` is controlled
by the source-specific telescope budget. -/
theorem cmp116SourcePi4FullComplexR1BilateralSchurRate_le_telescope
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K root : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (sigma : FinBox 4 (2 * Q) → ℂ) :
    cmp116SourcePi4FullComplexR1BilateralSchurRate
        (R := R) anchor K root hc hmass hK Z0 sigma ≤
      cmp116SourcePi4FullComplexR1TelescopeSchurBudget
        (R := R) anchor K root hc hmass hK Z0 sigma := by
  simpa [cmp116SourcePi4FullComplexR1BilateralSchurRate,
    cmp116SourcePi4FullComplexR1TelescopeSchurBudget,
    cmp116SourcePi4FullComplexR1Matrix] using
    (cmp116R1BilateralSchurRate_le_telescopeBudget
      (cmp116SourcePi4PhysicalBaseGammaMatrix K root Z0)
      (cmp116SourcePi4FullComplexGammaMatrix
        (R := R) anchor K root hc hmass hK Z0 sigma)
      (cmp116SourcePi4PhysicalBaseCovarianceMatrix K hc hmass hK)
      (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK sigma))

/-- The literal complex `R₁` quadratic is controlled by its generated
bilateral Schur rate, with no dimension factor and no supplied quadratic
inequality.  This is the global-energy form; localizing the right-hand side
to the physical contour carrier remains a separate source theorem. -/
theorem cmp116SourcePi4FullComplexR1_quadratic_re_le_bilateralSchurRate
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K root : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (x : CMP116Eq214GaussianCoordinate
      (PhysicalBond 4 (M * (2 * Q))) (Nc ^ 2 - 1)) :
    (cmp116Eq214ComplexQuadratic
      (cmp116SourcePi4FullComplexR1Matrix
        (R := R) anchor K root hc hmass hK Z0 sigma) x).re ≤
      cmp116SourcePi4FullComplexR1BilateralSchurRate
          (R := R) anchor K root hc hmass hK Z0 sigma *
        ∑ i, x i ^ 2 := by
  exact cmp116Eq214ComplexQuadratic_re_le_linfty_bilateral
    (cmp116SourcePi4FullComplexR1Matrix
      (R := R) anchor K root hc hmass hK Z0 sigma) x

end

end YangMills.RG
