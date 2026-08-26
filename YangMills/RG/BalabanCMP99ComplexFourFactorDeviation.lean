import YangMills.RG.BalabanCMP116FourFactorLipschitz

/-!
# Four-factor deviation for the complex CMP99 Ubar contour

The physical `SU(N)` estimate may add the four deviations because all four
factors have operator norm one.  That argument is false for the literal
`SL(N,C)` continuation.  This leaf keeps the norm budget of every complex
factor visible and specializes the already proved heterogeneous telescoping
identity against four identity matrices.

It is algebra only.  Path-product bounds and the identification of the fourth
factor with the inverse coarse holonomy remain downstream physical gates.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {Nc : ℕ} [NeZero Nc]

local instance cmp99ComplexFourFactorMatrixNormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- Exact budget left by telescoping four complex factors against the
identity.  The three preceding factor norms stay visible in every summand. -/
def cmp99ComplexFourFactorDeviationBudget
    (delta factorNorm : Fin 4 → ℝ) : ℝ :=
  delta 0 * factorNorm 1 * factorNorm 2 * factorNorm 3 +
  delta 1 * factorNorm 2 * factorNorm 3 +
  delta 2 * factorNorm 3 +
  delta 3

/-- Four complex factors close to one have the heterogeneous Ubar deviation
budget.  No unitarity, inverse-norm identity or common-radius weakening is
used. -/
theorem norm_fourMatrixProduct_sub_one_le_complexBudget
    (A : Fin 4 → Matrix (Fin Nc) (Fin Nc) ℂ)
    (delta factorNorm : Fin 4 → ℝ)
    (hdev : ∀ i, ‖A i - 1‖ ≤ delta i)
    (hnorm : ∀ i, ‖A i‖ ≤ factorNorm i) :
    ‖fourMatrixProduct A - 1‖ ≤
      cmp99ComplexFourFactorDeviationBudget delta factorNorm := by
  have hdelta : ∀ i, 0 ≤ delta i := fun i ↦
    (norm_nonneg (A i - 1)).trans (hdev i)
  have hfactorNorm : ∀ i, 0 ≤ factorNorm i := fun i ↦
    (norm_nonneg (A i)).trans (hnorm i)
  have hterm0 :
      ‖A 0 - 1‖ * ‖A 1‖ * ‖A 2‖ * ‖A 3‖ ≤
        delta 0 * factorNorm 1 * factorNorm 2 * factorNorm 3 := by
    have h01 : ‖A 0 - 1‖ * ‖A 1‖ ≤ delta 0 * factorNorm 1 :=
      mul_le_mul (hdev 0) (hnorm 1) (norm_nonneg _) (hdelta 0)
    have h012 : ‖A 0 - 1‖ * ‖A 1‖ * ‖A 2‖ ≤
        delta 0 * factorNorm 1 * factorNorm 2 :=
      mul_le_mul h01 (hnorm 2) (norm_nonneg _)
        (mul_nonneg (hdelta 0) (hfactorNorm 1))
    exact mul_le_mul h012 (hnorm 3) (norm_nonneg _)
      (mul_nonneg (mul_nonneg (hdelta 0) (hfactorNorm 1))
        (hfactorNorm 2))
  have hterm1 :
      ‖A 1 - 1‖ * ‖A 2‖ * ‖A 3‖ ≤
        delta 1 * factorNorm 2 * factorNorm 3 := by
    have h12 : ‖A 1 - 1‖ * ‖A 2‖ ≤ delta 1 * factorNorm 2 :=
      mul_le_mul (hdev 1) (hnorm 2) (norm_nonneg _) (hdelta 1)
    exact mul_le_mul h12 (hnorm 3) (norm_nonneg _)
      (mul_nonneg (hdelta 1) (hfactorNorm 2))
  have hterm2 :
      ‖A 2 - 1‖ * ‖A 3‖ ≤ delta 2 * factorNorm 3 := by
    exact mul_le_mul (hdev 2) (hnorm 3) (norm_nonneg _) (hdelta 2)
  have htel := norm_fourMatrixProduct_sub_le_heterogeneous
    A (fun _ : Fin 4 ↦ (1 : Matrix (Fin Nc) (Fin Nc) ℂ))
  calc
    ‖fourMatrixProduct A - 1‖ =
        ‖fourMatrixProduct A -
          fourMatrixProduct
            (fun _ : Fin 4 ↦ (1 : Matrix (Fin Nc) (Fin Nc) ℂ))‖ := by
      simp [fourMatrixProduct]
    _ ≤
        ‖A 0 - 1‖ * ‖A 1‖ * ‖A 2‖ * ‖A 3‖ +
        ‖A 1 - 1‖ * ‖A 2‖ * ‖A 3‖ +
        ‖A 2 - 1‖ * ‖A 3‖ +
        ‖A 3 - 1‖ := by
      simpa using htel
    _ ≤
        delta 0 * factorNorm 1 * factorNorm 2 * factorNorm 3 +
        delta 1 * factorNorm 2 * factorNorm 3 +
        delta 2 * factorNorm 3 +
        delta 3 := by
      exact add_le_add (add_le_add (add_le_add hterm0 hterm1) hterm2) (hdev 3)
    _ = cmp99ComplexFourFactorDeviationBudget delta factorNorm := rfl

end

end YangMills.RG
