import YangMills.ClayCore.SchurEntryOrthogonality
noncomputable section
open Matrix Complex MeasureTheory
open scoped BigOperators
namespace YangMills.ClayCore
variable {N : ℕ} [NeZero N]

lemma piAntiSymSU_apply_entry (i k : Fin N)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) (m j : Fin N) :
    ((piAntiSymSU i k * U).val) m j =
      Complex.exp (Complex.I * (piAntiSymAngle i k m : ℂ)) * U.val m j := by
  show ((diagPhaseSU (piAntiSymAngle i k) (piAntiSymAngle_sum_zero i k) * U).val) m j = _
  rw [diagPhaseSU_apply_entry]
  rfl

lemma piAntiSymSU_entry_prod_flip (i k : Fin N) (hik : i ≠ k) (j l : Fin N)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (piAntiSymSU i k * U).val i j * star ((piAntiSymSU i k * U).val k l) =
      -(U.val i j * star (U.val k l)) := by
  rw [piAntiSymSU_apply_entry, piAntiSymSU_apply_entry]
  have hstar :
      star (Complex.exp (Complex.I * (piAntiSymAngle i k k : ℂ)) * U.val k l) =
        star (U.val k l) *
          star (Complex.exp (Complex.I * (piAntiSymAngle i k k : ℂ))) :=
    StarMul.star_mul _ _
  rw [hstar]
  have h := piAntiSymSU_phase i k hik
  linear_combination (U.val i j * star (U.val k l)) * h

theorem sunHaarProb_entry_offdiag (i k : Fin N) (hik : i ≠ k) (j l : Fin N) :
    (∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N)) = 0 := by
  set I₀ := ∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N) with hI₀
  have hflip := piAntiSymSU_entry_prod_flip i k hik j l
  have hinv : I₀ = -I₀ := by
    calc I₀
        = ∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N) := hI₀
      _ = ∫ U, (piAntiSymSU i k * U).val i j *
            star ((piAntiSymSU i k * U).val k l) ∂(sunHaarProb N) :=
          (MeasureTheory.integral_mul_left_eq_self
            (μ := sunHaarProb N)
            (fun U => U.val i j * star (U.val k l))
            (piAntiSymSU i k)).symm
      _ = ∫ U, -(U.val i j * star (U.val k l)) ∂(sunHaarProb N) :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hflip)
      _ = -∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N) := integral_neg _
      _ = -I₀ := by rw [← hI₀]
  have h2I : (2 : ℂ) * I₀ = 0 := by
    have hdouble : (2 : ℂ) * I₀ = I₀ + I₀ := by ring
    rw [hdouble]
    nth_rw 2 [hinv]
    ring
  have h2ne : (2 : ℂ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp h2I).resolve_left h2ne

/-! ## Right-multiplication case: j ≠ l -/

/-- Entry formula for right-multiplication by a diagonal phase matrix. -/
lemma diagPhaseSU_apply_entry_right (θ : Fin N → ℝ) (hθ : ∑ k, θ k = 0)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) (m n : Fin N) :
    ((U * diagPhaseSU θ hθ).val) m n =
      Complex.exp (Complex.I * (θ n : ℂ)) * U.val m n := by
  show (U.val * (diagPhaseSU θ hθ).val) m n = _
  have hD : (diagPhaseSU θ hθ).val = Matrix.diagonal (diagPhaseVec θ) := rfl
  rw [hD, Matrix.mul_diagonal]
  exact mul_comm _ _

/-- Entry formula for right-multiplication by `piAntiSymSU j l`. -/
lemma piAntiSymSU_apply_entry_right (j l : Fin N)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) (m n : Fin N) :
    ((U * piAntiSymSU j l).val) m n =
      Complex.exp (Complex.I * (piAntiSymAngle j l n : ℂ)) * U.val m n :=
  diagPhaseSU_apply_entry_right _ (piAntiSymAngle_sum_zero j l) U m n

/-- After right-multiplying by `piAntiSymSU j l` (for j ≠ l), the product
    `U_ij · star(U_kl)` picks up a factor of `-1`. -/
lemma piAntiSymSU_entry_prod_flip_right (j l : Fin N) (hjl : j ≠ l)
    (i k : Fin N) (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (U * piAntiSymSU j l).val i j * star ((U * piAntiSymSU j l).val k l) =
      -(U.val i j * star (U.val k l)) := by
  rw [piAntiSymSU_apply_entry_right, piAntiSymSU_apply_entry_right]
  have hstar :
      star (Complex.exp (Complex.I * (piAntiSymAngle j l l : ℂ)) * U.val k l) =
        star (U.val k l) *
          star (Complex.exp (Complex.I * (piAntiSymAngle j l l : ℂ))) :=
    StarMul.star_mul _ _
  rw [hstar]
  have h := piAntiSymSU_phase j l hjl
  linear_combination (U.val i j * star (U.val k l)) * h

/-- Off-diagonal Haar integral vanishes for `j ≠ l` (right-invariance case).
Mirrors the pattern of `SchurOffDiagonal.sunHaarProb_offdiag_integral_zero`
via `sunHaarProb_isMulRightInvariant`. -/
theorem sunHaarProb_entry_offdiag_col (i k : Fin N) (j l : Fin N) (hjl : j ≠ l) :
    (∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N)) = 0 := by
  haveI hinv : (sunHaarProb N).IsMulRightInvariant :=
    sunHaarProb_isMulRightInvariant N
  set I₀ : ℂ := ∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N) with hI₀
  have hR :
      (∫ U, (U * piAntiSymSU j l).val i j *
            star ((U * piAntiSymSU j l).val k l) ∂(sunHaarProb N)) = I₀ := by
    rw [hI₀]
    exact MeasureTheory.integral_mul_right_eq_self
      (μ := sunHaarProb N)
      (fun U => U.val i j * star (U.val k l)) (piAntiSymSU j l)
  have hfun :
      (fun U : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        (U * piAntiSymSU j l).val i j *
          star ((U * piAntiSymSU j l).val k l))
      = fun U => -(U.val i j * star (U.val k l)) := by
    funext U
    exact piAntiSymSU_entry_prod_flip_right j l hjl i k U
  rw [hfun, MeasureTheory.integral_neg] at hR
  linear_combination (-(1 : ℂ) / 2) * hR

/-- Combined off-diagonal result: `∫ U_ij · star(U_kl) = 0` whenever `(i,j) ≠ (k,l)`. -/
theorem sunHaarProb_entry_offdiag_general (i k j l : Fin N)
    (hne : i ≠ k ∨ j ≠ l) :
    (∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N)) = 0 := by
  rcases hne with hik | hjl
  · exact sunHaarProb_entry_offdiag i k hik j l
  · exact sunHaarProb_entry_offdiag_col i k j l hjl
end YangMills.ClayCore