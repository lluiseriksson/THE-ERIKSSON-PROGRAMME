import YangMills.RG.BalabanCMP99ComplexSpecialLinearAdjointAction

/-!
PRE-VALIDATION: source present, `.olean` not yet materialized, and the result
has not yet been verified by the compiler or axiom oracle.

# Multiplicativity of the complex `SL(N,C)` adjoint action

The source-facing expansion of CMP99 (3.51) compares the adjoint action of
`exp(i eta A') U` with the baseline action of `U`.  This leaf records the
exact group law in the already sealed complex coordinate model.  It carries
no perturbation, norm or source-bound hypothesis.
-/

namespace YangMills.RG

noncomputable section

open Matrix

variable {Nc : Nat} [NeZero Nc]

/-- Literal inner conjugation is multiplicative in its group argument. -/
theorem cmp99SpecialLinearAdjointCoordLM_mul
    (g h : Matrix.SpecialLinearGroup (Fin Nc) ℂ)
    (Z : SUNLieComplexCoord Nc) :
    cmp99SpecialLinearAdjointCoordLM (g * h) Z =
      cmp99SpecialLinearAdjointCoordLM g
        (cmp99SpecialLinearAdjointCoordLM h Z) := by
  apply cmp99SUNLieComplexCoordMatrixLM_injective
  simp only [cmp99SUNLieComplexCoordMatrixLM_specialLinearAdjoint]
  change
    ((g * h : Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
        Matrix (Fin Nc) (Fin Nc) ℂ) *
          cmp99SUNLieComplexCoordMatrixLM Nc Z *
            (((g * h : Matrix.SpecialLinearGroup (Fin Nc) ℂ)⁻¹ :
              Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
                Matrix (Fin Nc) (Fin Nc) ℂ) =
      (g : Matrix (Fin Nc) (Fin Nc) ℂ) *
        ((h : Matrix (Fin Nc) (Fin Nc) ℂ) *
          cmp99SUNLieComplexCoordMatrixLM Nc Z *
            ((h⁻¹ : Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
              Matrix (Fin Nc) (Fin Nc) ℂ)) *
          ((g⁻¹ : Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
            Matrix (Fin Nc) (Fin Nc) ℂ)
  simp only [Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.mul_inv_rev]
  noncomm_ring

end

end YangMills.RG
