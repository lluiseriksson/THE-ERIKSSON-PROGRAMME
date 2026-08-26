import YangMills.RG.BalabanCMP99Eq337PhysicalComplexPerturbedBackground

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# Complex adjoint transport for the Eq. (3.59) two-tower bridge

The real retained tower transports `SUNLieCoord` by orthogonal maps.  That
interface cannot be reused after analytic continuation: an `SL(N,C)` bond is
invertible but need not act isometrically.  This file constructs the literal
complex-linear conjugation on the traceless matrix model and transports it
back through the already sealed `SUNLieComplexCoord <-> sl(N,C)` equivalence.

This is only the forward transport used to build `Q'(U)`.  It deliberately
does not call Lean's Hilbert adjoint the printed starred synthesis away from
the real slice; that independent construction remains a separate Eq. (3.59)
obligation.
-/

namespace YangMills.RG

noncomputable section

open Matrix

variable {Nc : Nat} [NeZero Nc]

/-- Literal conjugation by one `SL(N,C)` element on the traceless matrix
model. -/
def cmp99SpecialLinearAdjointSlLM
    (g : Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
    LieAlgebra.SpecialLinear.sl (Fin Nc) ℂ →ₗ[ℂ]
      LieAlgebra.SpecialLinear.sl (Fin Nc) ℂ where
  toFun X := by
    refine ⟨(g : Matrix (Fin Nc) (Fin Nc) ℂ) * X.1 *
        ((g⁻¹ : Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
          Matrix (Fin Nc) (Fin Nc) ℂ), ?_⟩
    change Matrix.trace
      ((g : Matrix (Fin Nc) (Fin Nc) ℂ) * X.1 *
        ((g⁻¹ : Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
          Matrix (Fin Nc) (Fin Nc) ℂ)) = 0
    rw [Matrix.trace_mul_cycle]
    have hg :
        (((g⁻¹ : Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
            Matrix (Fin Nc) (Fin Nc) ℂ) *
          (g : Matrix (Fin Nc) (Fin Nc) ℂ)) = 1 := by
      change (((g⁻¹ * g : Matrix.SpecialLinearGroup (Fin Nc) ℂ)) :
        Matrix (Fin Nc) (Fin Nc) ℂ) = 1
      simp
    have hX := X.2
    change Matrix.trace X.1 = 0 at hX
    rw [hg, Matrix.one_mul, hX]
  map_add' X Y := by
    apply Subtype.ext
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    apply Subtype.ext
    simp

/-- Coordinate form of the literal complex adjoint action. -/
def cmp99SpecialLinearAdjointCoordLM
    (g : Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
    SUNLieComplexCoord Nc →ₗ[ℂ] SUNLieComplexCoord Nc where
  toFun Z := (cmp99SUNLieComplexCoordSlEquiv Nc).symm
    (cmp99SpecialLinearAdjointSlLM g
      (cmp99SUNLieComplexCoordSlEquiv Nc Z))
  map_add' X Y := by simp
  map_smul' c X := by simp

@[simp] theorem cmp99SUNLieComplexCoordMatrixLM_specialLinearAdjoint
    (g : Matrix.SpecialLinearGroup (Fin Nc) ℂ)
    (Z : SUNLieComplexCoord Nc) :
    cmp99SUNLieComplexCoordMatrixLM Nc
        (cmp99SpecialLinearAdjointCoordLM g Z) =
      (g : Matrix (Fin Nc) (Fin Nc) ℂ) *
        cmp99SUNLieComplexCoordMatrixLM Nc Z *
          ((g⁻¹ : Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
            Matrix (Fin Nc) (Fin Nc) ℂ) := by
  change
    ((cmp99SUNLieComplexCoordSlEquiv Nc)
      ((cmp99SUNLieComplexCoordSlEquiv Nc).symm
        (cmp99SpecialLinearAdjointSlLM g
          (cmp99SUNLieComplexCoordSlEquiv Nc Z)))).1 = _
  rw [(cmp99SUNLieComplexCoordSlEquiv Nc).apply_symm_apply]
  rfl

end

end YangMills.RG
