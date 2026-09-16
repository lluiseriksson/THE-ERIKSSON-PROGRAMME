import YangMills.RG.BalabanCMP99ComplexMatrixInverseRegularity

namespace YangMills.RG

noncomputable section

def testMiddle
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : ℂ → Matrix ι ι ℂ) (Q : Matrix κ ι ℂ)
    (Qstar : Matrix ι κ ℂ) (u : ℂ) : Matrix κ κ ℂ :=
  (Q * C u) * Qstar

def testH
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ]
    (C : ℂ → Matrix ι ι ℂ) (Q : Matrix κ ι ℂ)
    (Qstar : Matrix ι κ ℂ) (u : ℂ) : Matrix ι κ ℂ :=
  (C u * Qstar) * (testMiddle C Q Qstar u)⁻¹

theorem testH_diff
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ]
    (C : ℂ → Matrix ι ι ℂ) (Q : Matrix κ ι ℂ)
    (Qstar : Matrix ι κ ℂ) (t : ℂ)
    (hC : ∀ i j, DifferentiableAt ℂ (fun u => C u i j) t)
    (hdet : (testMiddle C Q Qstar t).det ≠ 0)
    (row : ι) (col : κ) :
    DifferentiableAt ℂ (fun u => testH C Q Qstar u row col) t := by
  classical
  have hMiddle : ∀ i j,
      DifferentiableAt ℂ (fun u => testMiddle C Q Qstar u i j) t := by
    intro i j
    simp only [testMiddle, Matrix.mul_apply]
    apply DifferentiableAt.fun_sum
    intro k _
    apply DifferentiableAt.mul_const
    apply DifferentiableAt.fun_sum
    intro l _
    exact (hC l k).const_mul (Q i l)
  have hInv : ∀ i j,
      DifferentiableAt ℂ
        (fun u => (testMiddle C Q Qstar u)⁻¹ i j) t := by
    intro i j
    exact
      differentiableAt_complexMatrixNonsingInvEntry_of_entrywise
        (testMiddle C Q Qstar) t hMiddle hdet i j
  simp only [testH, Matrix.mul_apply]
  apply DifferentiableAt.fun_sum
  intro k _
  apply DifferentiableAt.mul
  · apply DifferentiableAt.fun_sum
    intro l _
    exact (hC row l).mul_const (Qstar l k)
  · exact hInv k col

end

end YangMills.RG
