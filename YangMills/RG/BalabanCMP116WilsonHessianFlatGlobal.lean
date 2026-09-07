import YangMills.RG.BalabanCMP116WilsonHessianFlatPlaquette

/-!
# Global flat Wilson Hessian

This module commutes the finite plaquette sum with both Fréchet derivatives
and consumes the exact local plaquette Hessian together with the flat
coordinate dictionary. The terminal theorem identifies the literal Wilson
Hessian at the trivial background with the global Hilbert form

`⟪D1 A, D1 B⟫`.

This is the Wilson-action component of the CMP99 flat precision operator.
Gauge fixing is deliberately kept separate.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

theorem ambientWilsonHessian_eq_sum_plaquetteHessian
    (U : PhysicalGaugeBackground d N Nc)
    (X Y : PhysicalAmbientMatrixTangent d N Nc) :
    ambientWilsonHessian U X Y =
      ∑ p : ConcretePlaquette d N,
        ambientWilsonPlaquetteHessian U p X Y := by
  have hfirst :
      fderiv ℝ (ambientWilsonAction U) =
        fun Z => ∑ p : ConcretePlaquette d N,
          fderiv ℝ (fun W => ambientWilsonPlaquetteAction U W p) Z := by
    funext Z
    unfold ambientWilsonAction
    exact (HasFDerivAt.fun_sum
      (𝕜 := ℝ)
      (u := (Finset.univ : Finset (ConcretePlaquette d N)))
      (A := fun p => fun W : PhysicalAmbientMatrixTangent d N Nc =>
        ambientWilsonPlaquetteAction U W p)
      (A' := fun p =>
        fderiv ℝ (fun W => ambientWilsonPlaquetteAction U W p) Z)
      (fun p hp =>
        (analyticAt_ambientWilsonPlaquetteAction U Z p).differentiableAt
          |>.hasFDerivAt)).fderiv
  unfold ambientWilsonHessian
  rw [hfirst]
  have hpiece (p : ConcretePlaquette d N) : HasFDerivAt
      (fun Z : PhysicalAmbientMatrixTangent d N Nc =>
        fderiv ℝ (fun W => ambientWilsonPlaquetteAction U W p) Z)
      (fderiv ℝ
        (fderiv ℝ (fun W => ambientWilsonPlaquetteAction U W p)) 0) 0 :=
    (analyticAt_ambientWilsonPlaquetteAction U 0 p).fderiv.differentiableAt
      |>.hasFDerivAt
  have hsecond := (HasFDerivAt.fun_sum
    (𝕜 := ℝ)
    (u := (Finset.univ : Finset (ConcretePlaquette d N)))
    (A := fun p => fun Z : PhysicalAmbientMatrixTangent d N Nc =>
      fderiv ℝ (fun W => ambientWilsonPlaquetteAction U W p) Z)
    (A' := fun p =>
      fderiv ℝ (fderiv ℝ
        (fun W => ambientWilsonPlaquetteAction U W p)) 0)
    (fun p hp => hpiece p)).fderiv
  simpa only [Finset.sum_apply, ContinuousLinearMap.sum_apply,
    ambientWilsonPlaquetteHessian] using congrArg (fun L => L X Y) hsecond

theorem ambientWilsonHessian_trivial_eq_inner_covariantD1
    (A B : PhysicalGaugeOneCochain d N Nc) :
    ambientWilsonHessian (trivialPhysicalGaugeBackground d N Nc)
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent A))
        (physicalSuTangentToAmbient
          (physicalCochainToSuMatrixTangent B)) =
      inner ℝ
        (covariantD1CLM (matrixSUNAdjointModel Nc)
          (trivialPhysicalGaugeBackground d N Nc) A)
        (covariantD1CLM (matrixSUNAdjointModel Nc)
          (trivialPhysicalGaugeBackground d N Nc) B) := by
  rw [ambientWilsonHessian_eq_sum_plaquetteHessian]
  simp_rw [ambientWilsonPlaquetteHessian_trivial]
  exact sum_matrixTraceInner_flatPlaquetteSuMatrixCurl_eq_inner_covariantD1 A B

theorem physicalWilsonHessian_trivial_eq_inner_covariantD1
    (A B : PhysicalGaugeOneCochain d N Nc) :
    physicalWilsonHessian (trivialPhysicalGaugeBackground d N Nc)
        (physicalCochainToSuMatrixTangent A)
        (physicalCochainToSuMatrixTangent B) =
      inner ℝ
        (covariantD1CLM (matrixSUNAdjointModel Nc)
          (trivialPhysicalGaugeBackground d N Nc) A)
        (covariantD1CLM (matrixSUNAdjointModel Nc)
          (trivialPhysicalGaugeBackground d N Nc) B) := by
  exact ambientWilsonHessian_trivial_eq_inner_covariantD1 A B

end

end YangMills.RG
