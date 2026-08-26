import YangMills.RG.BalabanCMP99ComplexSpecialLinearAdjointAction
import YangMills.RG.BalabanCMP98OrderedContourTransport

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# Compact real slice of the complex adjoint transport

This leaf constructs the canonical inclusion `SU(N) -> SL(N,C)` from the
same underlying matrix and proves that the analytic conjugation used by the
Eq. (3.59) tower restricts to the physical matrix adjoint action.  No lift or
matrix equality is supplied by the caller.
-/

namespace YangMills.RG

noncomputable section

open Matrix

variable {Nc : ℕ} [NeZero Nc]

/-- Canonical inclusion of the physical special-unitary group into the
complex special-linear group, with the underlying matrix unchanged. -/
def cmp99SUNToSpecialLinear (Nc : ℕ) [NeZero Nc] :
    SUN Nc →* Matrix.SpecialLinearGroup (Fin Nc) ℂ where
  toFun g := ⟨g.1, (Matrix.mem_specialUnitaryGroup_iff.mp g.2).2⟩
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rfl
  map_mul' g h := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rfl

@[simp] theorem cmp99SUNToSpecialLinear_coe
    (g : SUN Nc) :
    ((cmp99SUNToSpecialLinear Nc g :
        Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
      Matrix (Fin Nc) (Fin Nc) ℂ) = g.1 := by
  rfl

/-- On the compact subgroup, the inverse used by the algebraic `SL` action
is the conjugate transpose appearing in the physical adjoint action. -/
theorem cmp99SUNToSpecialLinear_inv_coe
    (g : SUN Nc) :
    ((((cmp99SUNToSpecialLinear Nc g)⁻¹ :
        Matrix.SpecialLinearGroup (Fin Nc) ℂ) :
      Matrix (Fin Nc) (Fin Nc) ℂ)) = g.1ᴴ := by
  rw [← map_inv]
  rfl

/-- The analytic `SL(N,C)` conjugation agrees exactly with the physical
adjoint model after the real Lie coordinate is complexified. -/
theorem cmp99SpecialLinearAdjointCoordLM_realSlice
    (g : SUN Nc) (X : SUNLieCoord Nc) :
    cmp99SpecialLinearAdjointCoordLM (cmp99SUNToSpecialLinear Nc g)
        (cmp99SUNLieCoordComplexificationLM Nc X) =
      cmp99SUNLieCoordComplexificationLM Nc
        ((matrixSUNAdjointModel Nc).adCLM g X) := by
  apply cmp99SUNLieComplexCoordMatrixLM_injective
  rw [cmp99SUNLieComplexCoordMatrixLM_specialLinearAdjoint,
    cmp99SUNLieComplexCoordMatrixLM_complexification,
    cmp99SUNLieComplexCoordMatrixLM_complexification,
    cmp98LieCoordMatrix_adCLM,
    cmp99SUNToSpecialLinear_coe,
    cmp99SUNToSpecialLinear_inv_coe]

/-- The independently constructed printed-star transport restricts to the
physical inverse adjoint action on the compact real slice.  This is an
equality of actions, not merely an equality of norms. -/
theorem cmp99SpecialLinearAdjointCoordLM_realSlice_inv
    (g : SUN Nc) (X : SUNLieCoord Nc) :
    cmp99SpecialLinearAdjointCoordLM (cmp99SUNToSpecialLinear Nc g)⁻¹
        (cmp99SUNLieCoordComplexificationLM Nc X) =
      cmp99SUNLieCoordComplexificationLM Nc
        ((matrixSUNAdjointModel Nc).adCLM g⁻¹ X) := by
  rw [← map_inv]
  exact cmp99SpecialLinearAdjointCoordLM_realSlice (g := g⁻¹) X

end

end YangMills.RG
