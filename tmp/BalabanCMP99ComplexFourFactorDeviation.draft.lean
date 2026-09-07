import YangMills.RG.BalabanCMP116FourFactorLipschitz

/-!
PRE-VALIDATION: this scratch source has no materialized `.olean` and no
compiler or axiom-oracle verdict.

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

variable {Nc : ℕ}

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
      gcongr
      · exact hdev 0
      · exact hnorm 1
      · exact hnorm 2
      · exact hnorm 3
      · exact hdev 1
      · exact hnorm 2
      · exact hnorm 3
      · exact hdev 2
      · exact hnorm 3
      · exact hdev 3
    _ = cmp99ComplexFourFactorDeviationBudget delta factorNorm := rfl

end

end YangMills.RG
