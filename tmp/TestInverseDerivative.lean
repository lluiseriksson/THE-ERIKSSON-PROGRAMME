import YangMills.RG.BalabanCMP99PhysicalRectangularMatrixReconstruction
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section

open YangMills.RG

theorem test_det_differentiable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℂ → Matrix ι ι ℂ) (t : ℂ)
    (hentry : ∀ i j, DifferentiableAt ℂ (fun u => M u i j) t) :
    DifferentiableAt ℂ (fun u => (M u).det) t := by
  classical
  simp_rw [Matrix.det_apply']
  fun_prop

theorem test_adjugate_entry_differentiable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℂ → Matrix ι ι ℂ) (t : ℂ)
    (hentry : ∀ i j, DifferentiableAt ℂ (fun u => M u i j) t)
    (row col : ι) :
    DifferentiableAt ℂ (fun u => (M u).adjugate row col) t := by
  classical
  simp_rw [Matrix.adjugate_apply]
  apply test_det_differentiable
  intro i j
  by_cases hij : i = col
  · subst i
    simp only [Matrix.updateRow_self]
    fun_prop
  · simpa [Matrix.updateRow_apply, hij] using hentry i j

theorem test_nonsing_inv_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    A⁻¹ = (A.det)⁻¹ • A.adjugate := by
  by_cases h : A.det = 0
  · rw [Matrix.nonsing_inv_apply_not_isUnit]
    · simp [h]
    · simpa [isUnit_iff_ne_zero, h]
  · rw [Matrix.nonsing_inv_apply
      (A := A) (isUnit_iff_ne_zero.mpr h)]
    simp [Units.val_inv_eq_inv_val]

theorem test_inverse_entry_differentiable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℂ → Matrix ι ι ℂ) (t : ℂ)
    (hentry : ∀ i j, DifferentiableAt ℂ (fun u => M u i j) t)
    (hdet : (M t).det ≠ 0)
    (row col : ι) :
    DifferentiableAt ℂ (fun u => (M u)⁻¹ row col) t := by
  rw [show (fun u => (M u)⁻¹ row col) =
      fun u => ((M u).det)⁻¹ * (M u).adjugate row col by
    funext u
    rw [test_nonsing_inv_eq (M u)]
    rfl]
  exact
    (test_det_differentiable M t hentry).inv hdet
      |>.mul (test_adjugate_entry_differentiable M t hentry row col)
