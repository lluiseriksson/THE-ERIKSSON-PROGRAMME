/- STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

This module constructs mass-uniform holomorphy and the physical boundary seam
for the literal CMP89 fine-lattice left-derivative integrand.  It introduces
no caller-supplied derivative family, endpoint identity or spacing premise:
the generated spacing is positive from `[NeZero L]`, and that fact is already
consumed inside the exact forward-difference theorem cited below. -/

import YangMills.RG.BalabanCMP89Eq248FineLatticeFourierGreenLeftDerivative
import YangMills.RG.BalabanCMP89Eq248GreenMassUniformHolomorphy

namespace YangMills.RG

noncomputable section

/-- The literal stabilized fine-lattice left derivative is holomorphic on the
same common polydisc as its two internally constructed Green endpoints. -/
theorem differentiableAt_cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand_massUniform_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    {p : Fin 4 → ℝ} (hp : ∀ nu, |p nu| ≤ Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ nu, (z nu).re = p nu)
    (himag : ∀ nu, |(z nu).im| ≤ rho)
    (mu : Fin 4) (endpointU : Fin 4 → ℤ) :
    DifferentiableAt ℂ (fun w : Fin 4 → ℂ =>
      cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
        L j mass a w mu endpointU) z := by
  let shiftedU := cmp89Eq248FineLatticeForwardCoordinateShift mu endpointU
  let xi := cmp89Eq249FineLatticeSpacing L j
  have hshifted : DifferentiableAt ℂ (fun w : Fin 4 → ℂ =>
      cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 L j mass a w
        (cmp89Eq249PhysicalFineLatticeDisplacement xi shiftedU)) z :=
    differentiableAt_cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_of_commonRadius_massUniform_draft
      ha hrho hamplitude hradius hwindow hmass hp hreal himag
  have hbase : DifferentiableAt ℂ (fun w : Fin 4 → ℂ =>
      cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 L j mass a w
        (cmp89Eq249PhysicalFineLatticeDisplacement xi endpointU)) z :=
    differentiableAt_cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_of_commonRadius_massUniform_draft
      ha hrho hamplitude hradius hwindow hmass hp hreal himag
  have hquotient : DifferentiableAt ℂ (fun w : Fin 4 → ℂ =>
      (cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 L j mass a w
          (cmp89Eq249PhysicalFineLatticeDisplacement xi shiftedU) -
        cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 L j mass a w
          (cmp89Eq249PhysicalFineLatticeDisplacement xi endpointU)) /
        (xi : ℂ)) z :=
    (hshifted.sub hbase).div_const (xi : ℂ)
  have hfunction :
      (fun w : Fin 4 → ℂ =>
        cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
          L j mass a w mu endpointU) =
      (fun w : Fin 4 → ℂ =>
        (cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 L j mass a w
            (cmp89Eq249PhysicalFineLatticeDisplacement xi shiftedU) -
          cmp89Eq248ComplexStabilizedGreenEndpointIntegrand 4 L j mass a w
            (cmp89Eq249PhysicalFineLatticeDisplacement xi endpointU)) /
          (xi : ℂ)) := by
    funext w
    exact (cmp89Eq248ComplexStabilizedGreenEndpoint_forwardDifference
      (L := L) (j := j) (mass := mass) (a := a) w mu endpointU).symm
  rw [hfunction]
  exact hquotient

/-- The derivative seam is derived by applying the mass-uniform Green seam
separately to the forward endpoint and the base endpoint. -/
theorem cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand_boundarySeam_massUniform_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (nu : Fin 4) {p : Fin 4 → ℝ}
    (hp : ∀ k, |p k| ≤ Real.pi) (hface : p nu = -Real.pi)
    {z : Fin 4 → ℂ} (hreal : ∀ k, (z k).re = p k)
    (himag : ∀ k, |(z k).im| ≤ rho)
    (mu : Fin 4) (endpointU : Fin 4 → ℤ) :
    cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
        L j mass a (cmp89Eq248PhysicalCoordinatePeriodShift nu z) mu endpointU =
      cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
        L j mass a z mu endpointU := by
  let shiftedU := cmp89Eq248FineLatticeForwardCoordinateShift mu endpointU
  let xi := cmp89Eq249FineLatticeSpacing L j
  have hshifted :=
    cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_physicalFine_boundarySeam_massUniform_draft
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow hmass nu hp hface hreal himag shiftedU
  have hbase :=
    cmp89Eq248ComplexStabilizedGreenEndpointIntegrand_physicalFine_boundarySeam_massUniform_draft
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow hmass nu hp hface hreal himag endpointU
  rw [← cmp89Eq248ComplexStabilizedGreenEndpoint_forwardDifference
      (L := L) (j := j) (mass := mass) (a := a)
      (cmp89Eq248PhysicalCoordinatePeriodShift nu z) mu endpointU,
    ← cmp89Eq248ComplexStabilizedGreenEndpoint_forwardDifference
      (L := L) (j := j) (mass := mass) (a := a) z mu endpointU]
  rw [hshifted, hbase]

end

end YangMills.RG
