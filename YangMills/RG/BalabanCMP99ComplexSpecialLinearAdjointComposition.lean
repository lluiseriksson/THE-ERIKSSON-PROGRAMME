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
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_mul_distrib]
  noncomm_ring

/-- The algebraic complex adjoint action of the identity is the identity.
This is recorded explicitly so source-facing stencil proofs do not depend on
an unfolding convention for the transported coordinate model. -/
@[simp] theorem cmp99SpecialLinearAdjointCoordLM_one
    (Z : SUNLieComplexCoord Nc) :
    cmp99SpecialLinearAdjointCoordLM
        (1 : Matrix.SpecialLinearGroup (Fin Nc) ℂ) Z = Z := by
  apply cmp99SUNLieComplexCoordMatrixLM_injective
  simp only [cmp99SUNLieComplexCoordMatrixLM_specialLinearAdjoint]
  simp

/-- Transport by `g` followed by transport by its inverse cancels exactly.
This is the cancellation used when the regional `D_U^* D_U` stencil is
rewritten as a sum over the two canonical bond orientations. -/
@[simp] theorem cmp99SpecialLinearAdjointCoordLM_inv_apply
    (g : Matrix.SpecialLinearGroup (Fin Nc) ℂ)
    (Z : SUNLieComplexCoord Nc) :
    cmp99SpecialLinearAdjointCoordLM g⁻¹
        (cmp99SpecialLinearAdjointCoordLM g Z) = Z := by
  rw [← cmp99SpecialLinearAdjointCoordLM_mul]
  simp

end

end YangMills.RG
