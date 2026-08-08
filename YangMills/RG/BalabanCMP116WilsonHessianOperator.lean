import YangMills.RG.BalabanCMP116WilsonHessianLocality
import YangMills.RG.RealBilinearRiesz

/-!
# Canonical operator represented by the literal Wilson Hessian

The literal Wilson Hessian was previously a continuous bilinear form on the
ambient matrix chart.  This module restricts it to physical cochains and uses
Fréchet--Riesz to obtain the canonical continuous operator on the physical
Hilbert space.

At the trivial background the operator itself, not merely its quadratic form,
is proved equal to `D1†D1`.  Adding the separately formalized gauge-fixing and
block-constraint masses therefore recovers the exact flat CMP116 precision as
an operator identity.
-/

namespace YangMills.RG

open Matrix
open scoped RealInnerProductSpace Matrix.Norms.L2Operator

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

@[simp]
theorem physicalCochainToSuMatrixTangent_add
    (A B : PhysicalGaugeOneCochain d N Nc) :
    physicalCochainToSuMatrixTangent (A + B) =
      physicalCochainToSuMatrixTangent A +
        physicalCochainToSuMatrixTangent B := by
  funext b
  simp [physicalCochainToSuMatrixTangent]

@[simp]
theorem physicalCochainToSuMatrixTangent_smul
    (r : ℝ) (A : PhysicalGaugeOneCochain d N Nc) :
    physicalCochainToSuMatrixTangent (r • A) =
      r • physicalCochainToSuMatrixTangent A := by
  funext b
  simp [physicalCochainToSuMatrixTangent]

/-- The literal Wilson Hessian restricted to physical cochain coordinates,
packaged as a bounded bilinear form. -/
noncomputable def physicalWilsonHessianBilinCLM
    (U : PhysicalGaugeBackground d N Nc) :
    PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A =>
        LinearMap.toContinuousLinearMap
          { toFun := fun B =>
              physicalWilsonHessian U
                (physicalCochainToSuMatrixTangent A)
                (physicalCochainToSuMatrixTangent B)
            map_add' := fun B C => by
              rw [physicalCochainToSuMatrixTangent_add]
              exact physicalWilsonHessian_add_right U
                (physicalCochainToSuMatrixTangent A)
                (physicalCochainToSuMatrixTangent B)
                (physicalCochainToSuMatrixTangent C)
            map_smul' := fun r B => by
              rw [physicalCochainToSuMatrixTangent_smul]
              change ambientWilsonHessian U
                  (physicalSuTangentToAmbient
                    (physicalCochainToSuMatrixTangent A))
                  (r • physicalSuTangentToAmbient
                    (physicalCochainToSuMatrixTangent B)) =
                r • ambientWilsonHessian U
                  (physicalSuTangentToAmbient
                    (physicalCochainToSuMatrixTangent A))
                  (physicalSuTangentToAmbient
                    (physicalCochainToSuMatrixTangent B))
              exact (ambientWilsonHessian U
                (physicalSuTangentToAmbient
                  (physicalCochainToSuMatrixTangent A))).map_smul r _ }
      map_add' := fun A B => by
        ext C
        rw [physicalCochainToSuMatrixTangent_add]
        exact physicalWilsonHessian_add_left U
          (physicalCochainToSuMatrixTangent A)
          (physicalCochainToSuMatrixTangent B)
          (physicalCochainToSuMatrixTangent C)
      map_smul' := fun r A => by
        ext B
        rw [physicalCochainToSuMatrixTangent_smul]
        change ambientWilsonHessian U
            (r • physicalSuTangentToAmbient
              (physicalCochainToSuMatrixTangent A))
            (physicalSuTangentToAmbient
              (physicalCochainToSuMatrixTangent B)) =
          r • ambientWilsonHessian U
            (physicalSuTangentToAmbient
              (physicalCochainToSuMatrixTangent A))
            (physicalSuTangentToAmbient
              (physicalCochainToSuMatrixTangent B))
        exact DFunLike.congr_fun ((ambientWilsonHessian U).map_smul r _) _ }

@[simp]
theorem physicalWilsonHessianBilinCLM_apply
    (U : PhysicalGaugeBackground d N Nc)
    (A B : PhysicalGaugeOneCochain d N Nc) :
    physicalWilsonHessianBilinCLM U A B =
      physicalWilsonHessian U
        (physicalCochainToSuMatrixTangent A)
        (physicalCochainToSuMatrixTangent B) := rfl

/-- The canonical physical Wilson-Hessian operator. -/
noncomputable def physicalWilsonHessianCLM
    (U : PhysicalGaugeBackground d N Nc) :
    PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc :=
  realBilinearRiesz (physicalWilsonHessianBilinCLM U)

@[simp]
theorem inner_physicalWilsonHessianCLM
    (U : PhysicalGaugeBackground d N Nc)
    (A B : PhysicalGaugeOneCochain d N Nc) :
    inner ℝ (physicalWilsonHessianCLM U A) B =
      physicalWilsonHessian U
        (physicalCochainToSuMatrixTangent A)
        (physicalCochainToSuMatrixTangent B) := by
  rw [physicalWilsonHessianCLM, inner_realBilinearRiesz]
  rfl

/-- The canonical literal Wilson-Hessian operator is symmetric at every
physical background. -/
theorem physicalWilsonHessianCLM_isSymmetric
    (U : PhysicalGaugeBackground d N Nc) :
    (physicalWilsonHessianCLM U : PhysicalGaugeOneCochain d N Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain d N Nc).IsSymmetric := by
  intro A B
  calc
    inner ℝ (physicalWilsonHessianCLM U A) B =
        physicalWilsonHessian U
          (physicalCochainToSuMatrixTangent A)
          (physicalCochainToSuMatrixTangent B) :=
      inner_physicalWilsonHessianCLM U A B
    _ = physicalWilsonHessian U
          (physicalCochainToSuMatrixTangent B)
          (physicalCochainToSuMatrixTangent A) :=
      physicalWilsonHessian_symm U _ _
    _ = inner ℝ (physicalWilsonHessianCLM U B) A :=
      (inner_physicalWilsonHessianCLM U B A).symm
    _ = inner ℝ A (physicalWilsonHessianCLM U B) :=
      real_inner_comm _ _

/-- Adjoint form of symmetry for downstream operator calculus. -/
theorem physicalWilsonHessianCLM_adjoint_eq
    (U : PhysicalGaugeBackground d N Nc) :
    (physicalWilsonHessianCLM U).adjoint =
      physicalWilsonHessianCLM U :=
  (physicalWilsonHessianCLM_isSymmetric U).clm_adjoint_eq

/-- Exact operator recovery of the flat Wilson Hessian. -/
theorem physicalWilsonHessianCLM_trivial_eq_curlMass :
    physicalWilsonHessianCLM
        (trivialPhysicalGaugeBackground d N Nc) =
      (covariantD1CLM (matrixSUNAdjointModel Nc)
          (trivialPhysicalGaugeBackground d N Nc)).adjoint.comp
        (covariantD1CLM (matrixSUNAdjointModel Nc)
          (trivialPhysicalGaugeBackground d N Nc)) := by
  apply ContinuousLinearMap.ext
  intro A
  apply ext_inner_right ℝ
  intro B
  rw [inner_physicalWilsonHessianCLM,
    physicalWilsonHessian_trivial_eq_inner_covariantD1,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]

/-- Wilson Hessian plus unit gauge-fixing mass is exactly the flat Hodge
operator, now as an equality of continuous operators. -/
theorem physicalWilsonHessianCLM_trivial_add_gaugeFixingMass_eq_flatGaugeHodge :
    physicalWilsonHessianCLM
        (trivialPhysicalGaugeBackground d N Nc)
      + gaugeFixingMassCLM (matrixSUNAdjointModel Nc)
          (trivialPhysicalGaugeBackground d N Nc) =
      flatGaugeHodgeK0CLM d N Nc (matrixSUNAdjointModel Nc) := by
  rw [physicalWilsonHessianCLM_trivial_eq_curlMass]
  rfl

variable {L N' : ℕ} [NeZero L] [NeZero N']

/-- **Operator-level WIL-H3 endpoint.** The flat physical precision assembled
from the literal Wilson-Hessian operator is definitionally the CMP116 base
precision used by the Gaussian reduction. -/
theorem gaugeFixedBasePrecision_physicalWilsonHessianCLM_trivial_eq :
    gaugeFixedBasePrecisionCLM
        (physicalWilsonHessianCLM
            (trivialPhysicalGaugeBackground d (L * N') Nc)
          + gaugeFixingMassCLM (matrixSUNAdjointModel Nc)
              (trivialPhysicalGaugeBackground d (L * N') Nc))
        (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N') =
      fun a =>
        gaugeFixedBasePrecisionCLM
          (flatGaugeHodgeK0CLM d (L * N') Nc (matrixSUNAdjointModel Nc))
          (flatBlockConstraintQCLM (d := d) (Nc := Nc) L N') a := by
  funext a
  rw [physicalWilsonHessianCLM_trivial_add_gaugeFixingMass_eq_flatGaugeHodge]

end

end YangMills.RG
