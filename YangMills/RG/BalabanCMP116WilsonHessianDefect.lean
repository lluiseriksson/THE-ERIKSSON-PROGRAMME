import YangMills.RG.BalabanCMP116WilsonHessianOperatorLocality

/-!
# Interacting Wilson-Hessian defect

This module fixes the exact operator whose small-background norm must be
estimated in the CMP116 interacting campaign:

`H_W(U) - H_W(1)`.

Before any quantitative estimate, the defect is proved symmetric and exactly
range two.  The future Lipschitz theorem can therefore focus entirely on the
local plaquette coefficient bound.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Literal interacting Wilson-Hessian defect relative to the trivial
background. -/
noncomputable def physicalWilsonHessianDefectCLM
    (U : PhysicalGaugeBackground d N Nc) :
    PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc :=
  physicalWilsonHessianCLM U -
    physicalWilsonHessianCLM
      (trivialPhysicalGaugeBackground d N Nc)

@[simp]
theorem physicalWilsonHessianDefectCLM_apply
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc) :
    physicalWilsonHessianDefectCLM U A =
      physicalWilsonHessianCLM U A -
        physicalWilsonHessianCLM
          (trivialPhysicalGaugeBackground d N Nc) A := rfl

@[simp]
theorem inner_physicalWilsonHessianDefectCLM
    (U : PhysicalGaugeBackground d N Nc)
    (A B : PhysicalGaugeOneCochain d N Nc) :
    inner ℝ (physicalWilsonHessianDefectCLM U A) B =
      physicalWilsonHessian U
          (physicalCochainToSuMatrixTangent A)
          (physicalCochainToSuMatrixTangent B) -
        physicalWilsonHessian
          (trivialPhysicalGaugeBackground d N Nc)
          (physicalCochainToSuMatrixTangent A)
          (physicalCochainToSuMatrixTangent B) := by
  rw [physicalWilsonHessianDefectCLM_apply, inner_sub_left,
    inner_physicalWilsonHessianCLM, inner_physicalWilsonHessianCLM]

/-- The defect vanishes at the trivial background. -/
@[simp]
theorem physicalWilsonHessianDefectCLM_trivial :
    physicalWilsonHessianDefectCLM
      (trivialPhysicalGaugeBackground d N Nc) = 0 := by
  simp [physicalWilsonHessianDefectCLM]

/-- The interacting defect remains symmetric. -/
theorem physicalWilsonHessianDefectCLM_isSymmetric
    (U : PhysicalGaugeBackground d N Nc) :
    (physicalWilsonHessianDefectCLM U :
      PhysicalGaugeOneCochain d N Nc →ₗ[ℝ]
        PhysicalGaugeOneCochain d N Nc).IsSymmetric := by
  intro A B
  calc
    inner ℝ (physicalWilsonHessianDefectCLM U A) B =
        physicalWilsonHessian U
            (physicalCochainToSuMatrixTangent A)
            (physicalCochainToSuMatrixTangent B) -
          physicalWilsonHessian
            (trivialPhysicalGaugeBackground d N Nc)
            (physicalCochainToSuMatrixTangent A)
            (physicalCochainToSuMatrixTangent B) :=
      inner_physicalWilsonHessianDefectCLM U A B
    _ = physicalWilsonHessian U
            (physicalCochainToSuMatrixTangent B)
            (physicalCochainToSuMatrixTangent A) -
          physicalWilsonHessian
            (trivialPhysicalGaugeBackground d N Nc)
            (physicalCochainToSuMatrixTangent B)
            (physicalCochainToSuMatrixTangent A) := by
      rw [physicalWilsonHessian_symm U,
        physicalWilsonHessian_symm
          (trivialPhysicalGaugeBackground d N Nc)]
    _ = inner ℝ (physicalWilsonHessianDefectCLM U B) A :=
      (inner_physicalWilsonHessianDefectCLM U B A).symm
    _ = inner ℝ A (physicalWilsonHessianDefectCLM U B) :=
      real_inner_comm _ _

/-- Adjoint form of defect symmetry. -/
theorem physicalWilsonHessianDefectCLM_adjoint_eq
    (U : PhysicalGaugeBackground d N Nc) :
    (physicalWilsonHessianDefectCLM U).adjoint =
      physicalWilsonHessianDefectCLM U :=
  (physicalWilsonHessianDefectCLM_isSymmetric U).clm_adjoint_eq

/-- The defect retains the exact range-two support of both Hessians. -/
theorem physicalWilsonHessianDefectCLM_finiteRange
    (U : PhysicalGaugeBackground d N Nc) :
    PhysicalCovarianceFiniteRange
      (physicalWilsonHessianDefectCLM U) physicalBondDist 2 := by
  intro source target v hfar
  rw [physicalWilsonHessianDefectCLM_apply]
  change physicalWilsonHessianCLM U
        (singlePhysicalBondCochain source v) target -
      physicalWilsonHessianCLM
        (trivialPhysicalGaugeBackground d N Nc)
        (singlePhysicalBondCochain source v) target = 0
  rw [
    physicalWilsonHessianCLM_finiteRange U source target v hfar,
    physicalWilsonHessianCLM_finiteRange
      (trivialPhysicalGaugeBackground d N Nc) source target v hfar,
    sub_zero]

end

end YangMills.RG
