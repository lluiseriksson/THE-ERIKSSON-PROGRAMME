import YangMills.RG.BalabanCMP116WilsonHessianDifferential

/-!
# Trace bounds for the matrix L2 operator norm

The local Wilson Hessian is the real trace of a matrix-valued mixed
variation.  This file records the finite-dimensional factor needed to pass
from the L2 operator norm to that scalar.
-/

namespace YangMills.RG

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {Nc : ℕ} [NeZero Nc]

/-- Every matrix entry is bounded by the L2 operator norm. -/
theorem norm_matrix_entry_le_l2_opNorm
    (A : Matrix (Fin Nc) (Fin Nc) ℂ) (i j : Fin Nc) :
    ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace ℂ (Fin Nc) :=
    EuclideanSpace.single j (1 : ℂ)
  let y : EuclideanSpace ℂ (Fin Nc) :=
    (EuclideanSpace.equiv (Fin Nc) ℂ).symm (A *ᵥ e)
  have hentry : ‖y i‖ ≤ ‖y‖ :=
    PiLp.norm_apply_le y i
  have hmul : ‖y‖ ≤ ‖A‖ * ‖e‖ :=
    A.l2_opNorm_mulVec e
  calc
    ‖A i j‖ = ‖y i‖ := by
      change ‖A i j‖ = ‖(A *ᵥ (e : Fin Nc → ℂ)) i‖
      rw [show (e : Fin Nc → ℂ) = Pi.single j (1 : ℂ) by rfl,
        Matrix.mulVec_single]
      simp
    _ ≤ ‖y‖ := hentry
    _ ≤ ‖A‖ * ‖e‖ := hmul
    _ = ‖A‖ := by
      simp [e, EuclideanSpace.norm_single]

/-- The real trace costs at most the matrix dimension in L2 operator norm. -/
theorem abs_ambientTraceReal_le_card_mul_norm
    (A : Matrix (Fin Nc) (Fin Nc) ℂ) :
    |ambientTraceReal A| ≤ (Nc : ℝ) * ‖A‖ := by
  unfold ambientTraceReal
  calc
    |∑ i : Fin Nc, (A i i).re|
        ≤ ∑ i : Fin Nc, |(A i i).re| := by
          simpa using
            (Finset.abs_sum_le_sum_abs
              (fun i : Fin Nc => (A i i).re) Finset.univ)
    _ ≤ ∑ _i : Fin Nc, ‖A‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact le_trans (Complex.abs_re_le_norm (A i i))
        (norm_matrix_entry_le_l2_opNorm A i i)
    _ = (Nc : ℝ) * ‖A‖ := by simp

end

end YangMills.RG
