import Mathlib
open scoped Matrix
variable {k : ℕ}

noncomputable def topRingMat (k : ℕ) :
    IsTopologicalRing (Matrix (Fin k) (Fin k) ℂ) :=
  @Matrix.topologicalRing (Fin k) ℂ _ _ _ _

noncomputable def matExp {k : ℕ} (X : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (Fin k) (Fin k) ℂ :=
  @NormedSpace.exp _ _ _ (topRingMat k) X

lemma matExp_conjTranspose (X : Matrix (Fin k) (Fin k) ℂ) :
    (matExp X)ᴴ = matExp Xᴴ := by
  simp only [matExp]; exact (Matrix.exp_conjTranspose X).symm

lemma matExp_add_of_commute (A B : Matrix (Fin k) (Fin k) ℂ) (h : Commute A B) :
    matExp (A + B) = matExp A * matExp B := by
  simp only [matExp]; exact Matrix.exp_add_of_commute A B h

lemma matExp_zero : matExp (0 : Matrix (Fin k) (Fin k) ℂ) = 1 := by
  simp only [matExp]; exact @NormedSpace.exp_zero _ _ _ (topRingMat k)

-- Commute via neg_mul / mul_neg (not ring — ring fails for SemiconjBy over Matrix)
lemma commute_neg_left (X : Matrix (Fin k) (Fin k) ℂ) : Commute (-X) X := by
  show -X * X = X * -X
  rw [neg_mul, mul_neg]

lemma commute_neg_right (X : Matrix (Fin k) (Fin k) ℂ) : Commute X (-X) := by
  show X * -X = -X * X
  rw [mul_neg, neg_mul]

-- conjTranspose of real smul skew
lemma conjTranspose_smul_skewHerm (X : Matrix (Fin k) (Fin k) ℂ)
    (hX : Xᴴ = -X) (t : ℝ) :
    ((t : ℂ) • X)ᴴ = -((t : ℂ) • X) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
             Matrix.neg_apply, star_mul', Complex.star_def, Complex.conj_ofReal]
  have h : (starRingEnd ℂ) (X j i) = -X i j := by
    change star (X j i) = (-X) i j
    simpa using congr_fun (congr_fun hX i) j
  rw [h]; ring

-- Unitary theorems
theorem matExp_skewHerm_unitary (X : Matrix (Fin k) (Fin k) ℂ) (hX : Xᴴ = -X) :
    (matExp X)ᴴ * matExp X = 1 := by
  rw [matExp_conjTranspose, hX,
      ← matExp_add_of_commute _ _ (commute_neg_left X),
      neg_add_cancel, matExp_zero]

theorem matExp_skewHerm_unitary_right (X : Matrix (Fin k) (Fin k) ℂ) (hX : Xᴴ = -X) :
    matExp X * (matExp X)ᴴ = 1 := by
  rw [matExp_conjTranspose, hX,
      ← matExp_add_of_commute _ _ (commute_neg_right X),
      add_neg_cancel, matExp_zero]

theorem matExp_smul_mem_unitaryGroup (X : Matrix (Fin k) (Fin k) ℂ)
    (hX : Xᴴ = -X) (t : ℝ) :
    matExp ((t : ℂ) • X) ∈ Matrix.unitaryGroup (Fin k) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change matExp ((t : ℂ) • X) * (matExp ((t : ℂ) • X))ᴴ = 1
  exact matExp_skewHerm_unitary_right _ (conjTranspose_smul_skewHerm X hX t)
