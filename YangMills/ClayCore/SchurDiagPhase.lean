/-
  YangMills/ClayCore/SchurDiagPhase.lean

  Diagonal phase element of SU(N):
      diagPhaseSU θ hθ  :=  diag(exp(I · θ₁), ..., exp(I · θ_N))
  for any real θ : Fin N → ℝ with ∑_k θ_k = 0.

  Generalizes `SchurTwoSitePhase` (the special case θ_i = π/2,
  θ_j = -π/2, θ_k = 0 otherwise gives diag(I, -I, 1, ..., 1)).

  Used in L2.6 step 1 to force off-diagonal entry-pair integrals
      ∫ U_{i,j} · conj(U_{k,l}) dHaar  =  0   when i ≠ k
  via left-invariance of the Haar measure on SU(N) against
  diagPhaseSU with θ chosen so θ_i ≠ θ_k (mod 2π).

  Status: no sorry, no new axioms.
  Oracle must remain [propext, Classical.choice, Quot.sound].
-/
import YangMills.ClayCore.SchurTwoSitePhase

noncomputable section

open Matrix Complex
open scoped BigOperators

namespace YangMills.ClayCore

variable {N : ℕ}

/-! ### Diagonal phase vector -/

/-- Diagonal vector of unit-modulus phases, `k ↦ exp(I · θ_k)`. -/
def diagPhaseVec (θ : Fin N → ℝ) : Fin N → ℂ := fun k =>
  Complex.exp (Complex.I * (θ k : ℂ))

@[simp] lemma diagPhaseVec_apply (θ : Fin N → ℝ) (k : Fin N) :
    diagPhaseVec θ k = Complex.exp (Complex.I * (θ k : ℂ)) := rfl

private lemma star_I_mul_ofReal (t : ℝ) :
    star (Complex.I * (t : ℂ)) = -(Complex.I * (t : ℂ)) := by
  show (starRingEnd ℂ) (Complex.I * (t : ℂ)) = -(Complex.I * (t : ℂ))
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

private lemma star_exp_I_ofReal (t : ℝ) :
    star (Complex.exp (Complex.I * (t : ℂ)))
      = Complex.exp (-(Complex.I * (t : ℂ))) := by
  have h : star (Complex.exp (Complex.I * (t : ℂ)))
      = Complex.exp (star (Complex.I * (t : ℂ))) := by
    show (starRingEnd ℂ) (Complex.exp (Complex.I * (t : ℂ)))
        = Complex.exp ((starRingEnd ℂ) (Complex.I * (t : ℂ)))
    exact (Complex.exp_conj _).symm
  rw [h, star_I_mul_ofReal]

/-- Each phase entry has unit modulus. -/
lemma diagPhaseVec_mul_star (θ : Fin N → ℝ) (k : Fin N) :
    diagPhaseVec θ k * star (diagPhaseVec θ k) = 1 := by
  unfold diagPhaseVec
  rw [star_exp_I_ofReal, ← Complex.exp_add]
  have h0 : Complex.I * (θ k : ℂ) + -(Complex.I * (θ k : ℂ)) = 0 := by ring
  rw [h0]
  exact Complex.exp_zero

/-- Product of phase entries equals `exp(I · ∑ θ_k)`. -/
lemma diagPhaseVec_prod (θ : Fin N → ℝ) :
    (∏ k, diagPhaseVec θ k)
      = Complex.exp (Complex.I * ((∑ k, θ k : ℝ) : ℂ)) := by
  unfold diagPhaseVec
  rw [← Complex.exp_sum]
  congr 1
  rw [← Finset.mul_sum]
  push_cast
  rfl

/-- When `∑ θ = 0`, the product of phases is `1`. -/
lemma diagPhaseVec_prod_eq_one (θ : Fin N → ℝ) (hθ : ∑ k, θ k = 0) :
    (∏ k, diagPhaseVec θ k) = 1 := by
  rw [diagPhaseVec_prod, hθ]
  simp

/-! ### Diagonal phase matrix -/

/-- Diagonal matrix with phase entries. -/
def diagPhaseMat (θ : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (diagPhaseVec θ)

lemma diagPhaseMat_det (θ : Fin N → ℝ) (hθ : ∑ k, θ k = 0) :
    (diagPhaseMat θ).det = 1 := by
  unfold diagPhaseMat
  rw [Matrix.det_diagonal]
  exact diagPhaseVec_prod_eq_one θ hθ

lemma diagPhaseMat_mul_conjTranspose (θ : Fin N → ℝ) :
    diagPhaseMat θ * (diagPhaseMat θ).conjTranspose = 1 := by
  unfold diagPhaseMat
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  have hfun :
      (fun k => diagPhaseVec θ k * (star (diagPhaseVec θ)) k)
        = fun _ : Fin N => (1 : ℂ) := by
    funext k
    exact diagPhaseVec_mul_star θ k
  rw [hfun]
  exact Matrix.diagonal_one

/-! ### Promotion to SU(N) -/

/-- Diagonal phase element of `SU(N)`, parametrized by traceless real θ. -/
def diagPhaseSU (θ : Fin N → ℝ) (hθ : ∑ k, θ k = 0) :
    Matrix.specialUnitaryGroup (Fin N) ℂ :=
  ⟨diagPhaseMat θ, by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, diagPhaseMat_det θ hθ⟩
    rw [Matrix.mem_unitaryGroup_iff]
    exact diagPhaseMat_mul_conjTranspose θ⟩

@[simp] lemma diagPhaseSU_val (θ : Fin N → ℝ) (hθ : ∑ k, θ k = 0) :
    (diagPhaseSU θ hθ).val = diagPhaseMat θ := rfl

/-! ### Action on entries -/

/-- Left-multiplication by `diagPhaseSU θ` scales the `(k, j)` entry
    of any `U ∈ SU(N)` by `diagPhaseVec θ k = exp(I · θ_k)`. -/
lemma diagPhaseSU_apply_entry (θ : Fin N → ℝ) (hθ : ∑ k, θ k = 0)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) (k j : Fin N) :
    ((diagPhaseSU θ hθ * U).val) k j
      = diagPhaseVec θ k * U.val k j := by
  have hmul : ((diagPhaseSU θ hθ * U).val : Matrix (Fin N) (Fin N) ℂ)
      = (diagPhaseSU θ hθ).val * U.val := rfl
  rw [hmul, diagPhaseSU_val]
  show (diagPhaseMat θ * U.val) k j = diagPhaseVec θ k * U.val k j
  unfold diagPhaseMat
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · rw [Matrix.diagonal_apply_eq]
  · intro b _ hbk
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hbk)]; ring
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- Specialization to the `k`-th diagonal entry. -/
lemma diagPhaseSU_apply_diag (θ : Fin N → ℝ) (hθ : ∑ k, θ k = 0)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) (k : Fin N) :
    ((diagPhaseSU θ hθ * U).val) k k
      = diagPhaseVec θ k * U.val k k :=
  diagPhaseSU_apply_entry θ hθ U k k

end YangMills.ClayCore

end