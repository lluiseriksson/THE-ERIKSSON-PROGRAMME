/- STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

Mass-uniform real-slice recombination for the source-normalized raw endpoint
difference at the `alpha = 0` specialization underlying CMP89 (2.49).  This
removes the strictly-positive-mass premise from the exact endpoint-kernel
difference used by H5; it does not yet insert the physical Holder factor
`xi^(-alpha)`, prove a contour bound, an owner metric dictionary, regional B0,
window 15 or a terminal field.
-/

import YangMills.RG.BalabanCMP89Eq249FineLatticeLeftDerivativeProductContourTelescope
import YangMills.RG.BalabanCMP89Eq249FineLatticeStabilizedFourierLeftDerivativeKernel

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- The source-normalized `alpha = 0` real-slice integral is the literal
difference of its two internally constructed fine Fourier left-derivative
kernels under the mass-uniform window.  In particular this theorem specializes
to `mass = 0`; no positive-mass premise and no mass limit are used. -/
theorem
    cmp89Eq249NormalizedFineLatticeStabilizedIntegral_eq_fourierLeftDerivativeDiff_massUniform_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (holderU transportU : Fin 4 → ℤ) :
    cmp89Eq249NormalizedFineLatticeStabilizedIntegral
        L j mass a mu holderU transportU =
      cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel
          L j mass a mu (fun nu => holderU nu + transportU nu) -
        cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel
          L j mass a mu transportU := by
  let firstU : Fin 4 → ℤ := fun nu => holderU nu + transportU nu
  let holderDisplacement : Fin 4 → ℝ :=
    cmp89Eq249PhysicalFineLatticeDisplacement
      (cmp89Eq249FineLatticeSpacing L j) holderU
  let transportDisplacement : Fin 4 → ℝ :=
    cmp89Eq249PhysicalFineLatticeDisplacement
      (cmp89Eq249FineLatticeSpacing L j) transportU
  let productMeasure : Measure (Fin 4 → ℝ) :=
    Measure.pi fun _ : Fin 4 => volume.restrict (Set.uIoc 0 (2 * Real.pi))
  have hfirstKernelIntegrable : Integrable (fun x : Fin 4 → ℝ =>
      cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
        L j mass a
        (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
        mu firstU) productMeasure := by
    simpa [productMeasure,
      cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_draft,
      cmp89Eq251EndpointPartialSignedContourMomentum_zero] using
      (integrable_cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_draft
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho hamplitude hradius hwindow hmass 0 mu firstU)
  have hsecondKernelIntegrable : Integrable (fun x : Fin 4 → ℝ =>
      cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
        L j mass a
        (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
        mu transportU) productMeasure := by
    simpa [productMeasure,
      cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_draft,
      cmp89Eq251EndpointPartialSignedContourMomentum_zero] using
      (integrable_cmp89Eq249FineLatticeLeftDerivativePartialProductIntegrand_draft
        (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
        ha hrho hamplitude hradius hwindow hmass 0 mu transportU)
  have hadd :
      cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) firstU =
        fun nu => holderDisplacement nu + transportDisplacement nu := by
    simpa [firstU, holderDisplacement, transportDisplacement] using
      (cmp89Eq249PhysicalFineLatticeDisplacement_add
        (cmp89Eq249FineLatticeSpacing L j) holderU transportU)
  have hintegral :
      (∫ x, cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a 0
          (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)) mu
          holderDisplacement transportDisplacement ∂productMeasure) =
        (∫ x,
          cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
            L j mass a
            (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
            mu firstU ∂productMeasure) -
          ∫ x,
            cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
              L j mass a
              (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
              mu transportU ∂productMeasure := by
    rw [← integral_sub hfirstKernelIntegrable hsecondKernelIntegrable]
    apply integral_congr_ae
    filter_upwards with x
    have hsplit := cmp89Eq251ComplexStabilizedIntegrand_eq_sub_endpoint
      (L := L) (j := j) (mass := mass) (a := a) (alpha := 0)
      (z := fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
      (mu := mu) holderDisplacement transportDisplacement
    rw [← hadd] at hsplit
    rw [hsplit]
    rw [cmp89Eq251ComplexStabilizedEndpointIntegrand_zero_eq_fineFourierLeftDerivative
      (L := L) (j := j) (mass := mass) (a := a)
      (z := fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
      mu holderU firstU]
    exact congrArg₂ (fun p q : ℂ => p - q) rfl
      (cmp89Eq251ComplexStabilizedEndpointIntegrand_zero_eq_fineFourierLeftDerivative
        (L := L) (j := j) (mass := mass) (a := a)
        (z := fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
        mu holderU transportU)
  unfold cmp89Eq249NormalizedFineLatticeStabilizedIntegral
    cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel
    cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
    cmp89Eq249FourDimensionalBrillouinMeasure
  simp only [firstU, holderDisplacement, transportDisplacement] at hintegral ⊢
  rw [← mul_sub]
  exact congrArg
    (fun z : ℂ => ((((2 * Real.pi) ^ 4)⁻¹ : ℝ) : ℂ) * z) hintegral

end

end YangMills.RG
