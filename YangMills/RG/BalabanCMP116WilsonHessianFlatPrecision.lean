import YangMills.RG.BalabanCMP116WilsonHessianFlatGlobal
import YangMills.RG.GaugeFixedPrecision

/-!
# Exact flat Wilson-plus-gauge precision

The literal Wilson Hessian at the trivial background was identified in
`BalabanCMP116WilsonHessianFlatGlobal` with the curl form

`⟪D1 A, D1 B⟫`.

This module adds, as separate mathematical operations,

* the soft gauge-fixing form `⟪div A, div B⟫`;
* the block-constraint form `a ⟪Q A, Q B⟫`.

The terminal theorem identifies their sum with the already used physical
precision operator

`gaugeFixedBasePrecisionCLM flatGaugeHodgeK0CLM Q a`.

Thus the flat operator entering the CMP116 Gaussian reduction is no longer
only a supplied physical shell: its Wilson-action component is the literal
Fréchet Hessian, while gauge fixing and the block mass are added explicitly.

No claim is made here about a nontrivial background, the contour-dependent
Hessian, or the random-walk expansion.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- The bilinear form of the positive gauge-fixing mass is the inner product
of the two gauge constraints. -/
theorem gaugeFixingMass_inner_two
    (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (A B : PhysicalGaugeOneCochain d N Nc) :
    inner ℝ (gaugeFixingMassCLM ρ U A) B =
      inner ℝ (gaugeConstraintQCLM ρ U A)
        (gaugeConstraintQCLM ρ U B) := by
  rw [gaugeFixingMassCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]

/-- The literal flat Wilson Hessian plus the separately defined gauge-fixing
form is exactly the bilinear form of the flat Hodge operator. -/
theorem physicalWilsonHessian_trivial_add_gaugeFixing_eq_inner_flatGaugeHodge
    (A B : PhysicalGaugeOneCochain d N Nc) :
    physicalWilsonHessian (trivialPhysicalGaugeBackground d N Nc)
        (physicalCochainToSuMatrixTangent A)
        (physicalCochainToSuMatrixTangent B)
      + inner ℝ
          (gaugeFixingMassCLM (matrixSUNAdjointModel Nc)
            (trivialPhysicalGaugeBackground d N Nc) A) B =
      inner ℝ
        (flatGaugeHodgeK0CLM d N Nc (matrixSUNAdjointModel Nc) A) B := by
  rw [physicalWilsonHessian_trivial_eq_inner_covariantD1]
  rw [flatGaugeHodgeK0CLM, backgroundGaugeHodgeK0CLM,
    ContinuousLinearMap.add_apply, inner_add_left,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]

variable {L N' : ℕ} [NeZero L] [NeZero N']

/-- The literal bilinear form obtained from the flat Wilson Hessian, soft
gauge fixing, and the CMP96/CMP116 block-constraint mass. -/
def flatWilsonGaugeBlockBilinearForm
    (a : ℝ)
    (A B : FinePhysicalOneCochain d L N' Nc) : ℝ :=
  physicalWilsonHessian
      (trivialPhysicalGaugeBackground d (L * N') Nc)
      (physicalCochainToSuMatrixTangent A)
      (physicalCochainToSuMatrixTangent B)
    + inner ℝ
        (gaugeFixingMassCLM (matrixSUNAdjointModel Nc)
          (trivialPhysicalGaugeBackground d (L * N') Nc) A) B
    + a * inner ℝ
        (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N' A)
        (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N' B)

/-- **WIL-H3 terminal theorem.** The literal flat Wilson-plus-gauge bilinear
form is exactly the form represented by the physical CMP116 base precision.
-/
theorem flatWilsonGaugeBlockBilinearForm_eq_inner_flatBasePrecision
    (a : ℝ)
    (A B : FinePhysicalOneCochain d L N' Nc) :
    flatWilsonGaugeBlockBilinearForm a A B =
      inner ℝ
        (gaugeFixedBasePrecisionCLM
          (flatGaugeHodgeK0CLM d (L * N') Nc (matrixSUNAdjointModel Nc))
          (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N') a A) B := by
  rw [flatWilsonGaugeBlockBilinearForm,
    physicalWilsonHessian_trivial_add_gaugeFixing_eq_inner_flatGaugeHodge]
  rw [gaugeFixedBasePrecisionCLM, ContinuousLinearMap.add_apply,
    inner_add_left, ContinuousLinearMap.smul_apply, inner_smul_left,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]
  simp

/-- Diagonal energy form of the exact flat precision identity. -/
theorem flatWilsonGaugeBlockBilinearForm_self
    (a : ℝ)
    (A : FinePhysicalOneCochain d L N' Nc) :
    flatWilsonGaugeBlockBilinearForm a A A =
      ‖covariantD1CLM (matrixSUNAdjointModel Nc)
          (trivialPhysicalGaugeBackground d (L * N') Nc) A‖ ^ 2
        + ‖gaugeConstraintQCLM (matrixSUNAdjointModel Nc)
            (trivialPhysicalGaugeBackground d (L * N') Nc) A‖ ^ 2
        + a * ‖flatBlockConstraintQCLM
            (d := d) (Nc := Nc) L N' A‖ ^ 2 := by
  rw [flatWilsonGaugeBlockBilinearForm,
    physicalWilsonHessian_trivial_eq_inner_covariantD1,
    real_inner_self_eq_norm_sq, gaugeFixingMass_inner,
    real_inner_self_eq_norm_sq]

end

end YangMills.RG
