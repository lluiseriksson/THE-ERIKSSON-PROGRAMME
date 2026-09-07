import YangMills.RG.BalabanCMP99ComplexUbarSpecialLinear

/-!
PRE-VALIDATION: this scratch source has no materialized `.olean` and no
compiler or axiom-oracle verdict.

# Near-identity inversion in `SL(N,C)`

The negative orientation of a complex gauge configuration is reconstructed
by group inversion.  Unlike `SU(N)`, inversion is not an isometry here.  This
module keeps the exact geometric loss `r / (1-r)` visible.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {Nc : ℕ} [NeZero Nc]

local instance matrixL2CStarAlgebraForComplexInverseRadius :
    CStarAlgebra (Matrix (Fin Nc) (Fin Nc) ℂ) where

/-- If a determinant-one complex matrix is within radius `r < 1` of one,
its group inverse is within `r / (1-r)` of one.  The proof uses only the exact
group inverse identity and submultiplicativity; no unitary weakening occurs. -/
theorem norm_cmp99SpecialLinear_inv_sub_one_le_div
    (U : Matrix.SpecialLinearGroup (Fin Nc) ℂ)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hU : ‖(U : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ r) :
    ‖(U⁻¹ : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤
      r / (1 - r) := by
  let A : Matrix (Fin Nc) (Fin Nc) ℂ := U
  let V : Matrix (Fin Nc) (Fin Nc) ℂ := U⁻¹
  have hmul : A * V = 1 := by
    simpa [A, V] using congrArg
      (fun W : Matrix.SpecialLinearGroup (Fin Nc) ℂ ↦
        (W : Matrix (Fin Nc) (Fin Nc) ℂ))
      (mul_inv_cancel U)
  have hVeq : V = 1 + (1 - A) * V := by
    noncomm_ring [hmul]
  have hA : ‖1 - A‖ ≤ r := by
    simpa [A, norm_sub_rev] using hU
  have hVnorm : ‖V‖ ≤ (1 - r)⁻¹ := by
    have hraw : ‖V‖ ≤ 1 + r * ‖V‖ := by
      calc
        ‖V‖ = ‖1 + (1 - A) * V‖ := congrArg norm hVeq
        _ ≤ ‖(1 : Matrix (Fin Nc) (Fin Nc) ℂ)‖ +
            ‖(1 - A) * V‖ := norm_add_le _ _
        _ ≤ 1 + r * ‖V‖ := by
          rw [norm_one]
          exact add_le_add le_rfl
            ((norm_mul_le (1 - A) V).trans
              (mul_le_mul_of_nonneg_right hA (norm_nonneg V)))
    have hden : 0 < 1 - r := sub_pos.mpr hr1
    calc
      ‖V‖ ≤ 1 / (1 - r) := (le_div_iff₀ hden).2 (by
        nlinarith [norm_nonneg V])
      _ = (1 - r)⁻¹ := by simp [div_eq_mul_inv]
  have hdevEq : V - 1 = (1 - A) * V := by
    noncomm_ring [hmul]
  change ‖V - 1‖ ≤ r / (1 - r)
  rw [hdevEq]
  calc
    ‖(1 - A) * V‖ ≤ ‖1 - A‖ * ‖V‖ := norm_mul_le _ _
    _ ≤ r * (1 - r)⁻¹ :=
      mul_le_mul hA hVnorm (norm_nonneg V) hr0
    _ = r / (1 - r) := by rw [div_eq_mul_inv]

end

end YangMills.RG
