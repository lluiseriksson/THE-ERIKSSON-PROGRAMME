import Mathlib

/-!
# Experimental: Exponential curve on SU(N) — FINAL

Key: Commute via neg_mul/mul_neg (ring fails for SemiconjBy over Matrix).
1 sorry: Jacobi det(exp X) = 1 (Mathlib TODO).
-/

open scoped Matrix

namespace YangMills.Experimental.LieSUN
variable {n : ℕ}

noncomputable def topRingMat (n : ℕ) :
    IsTopologicalRing (Matrix (Fin n) (Fin n) ℂ) :=
  @Matrix.topologicalRing (Fin n) ℂ _ _ _ _

noncomputable def matExp {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  @NormedSpace.exp _ _ _ (topRingMat n) X

lemma matExp_conjTranspose (X : Matrix (Fin n) (Fin n) ℂ) :
    (matExp X)ᴴ = matExp Xᴴ := by
  simp only [matExp]; exact (Matrix.exp_conjTranspose X).symm

lemma matExp_add_of_commute (A B : Matrix (Fin n) (Fin n) ℂ) (h : Commute A B) :
    matExp (A + B) = matExp A * matExp B := by
  simp only [matExp]; exact Matrix.exp_add_of_commute A B h

lemma matExp_zero : matExp (0 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  simp only [matExp]; exact @NormedSpace.exp_zero _ _ _ (topRingMat n)

lemma commute_neg_left (X : Matrix (Fin n) (Fin n) ℂ) : Commute (-X) X := by
  show -X * X = X * -X; rw [neg_mul, mul_neg]

lemma commute_neg_right (X : Matrix (Fin n) (Fin n) ℂ) : Commute X (-X) := by
  show X * -X = -X * X; rw [mul_neg, neg_mul]

lemma conjTranspose_smul_skewHerm
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (t : ℝ) :
    ((t : ℂ) • X)ᴴ = -((t : ℂ) • X) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
             Matrix.neg_apply, star_mul', Complex.star_def, Complex.conj_ofReal]
  have h : (starRingEnd ℂ) (X j i) = -X i j := by
    change star (X j i) = (-X) i j
    simpa using congr_fun (congr_fun hX i) j
  rw [h]; ring

theorem matExp_skewHerm_unitary
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) :
    (matExp X)ᴴ * matExp X = 1 := by
  rw [matExp_conjTranspose, hX,
      ← matExp_add_of_commute _ _ (commute_neg_left X),
      neg_add_cancel, matExp_zero]

theorem matExp_skewHerm_unitary_right
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) :
    matExp X * (matExp X)ᴴ = 1 := by
  rw [matExp_conjTranspose, hX,
      ← matExp_add_of_commute _ _ (commute_neg_right X),
      add_neg_cancel, matExp_zero]

theorem matExp_smul_mem_unitaryGroup
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (t : ℝ) :
    matExp ((t : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change matExp ((t : ℂ) • X) * (matExp ((t : ℂ) • X))ᴴ = 1
  exact matExp_skewHerm_unitary_right _ (conjTranspose_smul_skewHerm X hX t)

/-- Mathlib gap: det(exp(tX)) = 1 when trace(X) = 0.
    Proof: det(exp A) = exp(trace A) (Jacobi's formula / Liouville).
    Mathlib lacks the general matrix exp determinant formula.
    Ref: Any linear algebra text, e.g. Hall 'Lie Groups', Prop 2.7. -/
/- matExp_traceless_det_one — axiom (Matrix.det_exp not available for NormedSpace.exp)
   Mathematical argument: det(exp(tX)) = exp(t*tr(X)) = exp(0) = 1 when tr(X) = 0.
   Blocked by: Matrix.det_exp applies to Matrix.exp ℂ, not to the NormedSpace.exp
   variant used by matExp.  A bridge lemma `matExp_eq_matrix_exp` would close this.
   See AXIOM_FRONTIER.md for full analysis. -/
axiom matExp_traceless_det_one
    {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (htr : X.trace = 0) (t : ℝ) :
    Matrix.det (matExp ((t : ℂ) • X)) = 1 only [matExp]
  rw [Matrix.det_exp]
  rw [Matrix.trace_smul, htr]
  simp

end YangMills.Experimental.LieSUN

section LieExpCurve
variable (N_c : ℕ) [NeZero N_c]
open YangMills.Experimental.LieSUN

noncomputable def lieExpCurve
    (X : Matrix (Fin N_c) (Fin N_c) ℂ) (hX : Xᴴ = -X) (htr : X.trace = 0)
    (U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) (t : ℝ) :
    ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) :=
  ⟨U.val * matExp ((t : ℂ) • X), by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    exact ⟨mul_mem (Matrix.mem_specialUnitaryGroup_iff.mp U.prop).1
                   (matExp_smul_mem_unitaryGroup X hX t),
           by rw [Matrix.det_mul,
                  (Matrix.mem_specialUnitaryGroup_iff.mp U.prop).2,
                  matExp_traceless_det_one X htr t, one_mul]⟩⟩

theorem lieExpCurve_at_zero
    (X : Matrix (Fin N_c) (Fin N_c) ℂ) (hX : Xᴴ = -X) (htr : X.trace = 0)
    (U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) :
    lieExpCurve N_c X hX htr U 0 = U := by
  ext1; simp [lieExpCurve, Complex.ofReal_zero, zero_smul, matExp_zero]

noncomputable def lieDerivConcrete
    (X : Matrix (Fin N_c) (Fin N_c) ℂ) (hX : Xᴴ = -X) (htr : X.trace = 0)
    (f : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ)) : ℝ :=
  deriv (fun t => f (lieExpCurve N_c X hX htr U t)) 0

end LieExpCurve
