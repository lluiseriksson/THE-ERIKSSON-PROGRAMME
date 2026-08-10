/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249FineLatticeNormalizedStabilizedIntegralRecombination

/-!
# PRE-VALIDATION: fine-lattice Fourier left-derivative kernel

Source is present at this checkpoint, but its `.olean` has not yet been
materialized and the result has not yet been verified by the Lean compiler.

CMP89 (2.49) evaluates the left-derivative kernel at physical fine-lattice
displacements `xi*u`, with `xi = (L^j)^(-1)`.  The previously sealed
integer-displacement Fourier kernel lives at the wrong phase scale and is not
imported here.

At the literal `alpha = 0` specialization the endpoint branch is independent
of its Holder displacement.  This module uses that exact fact to construct a
separate fine-lattice Fourier endpoint, prove equality with every physical
fine endpoint, and rewrite the complete normalized stabilized expression as
the difference of two internally constructed fine kernels.

The identification of this Fourier definition with the repository's literal
operator `partial_mu^xi (G_j Q_j^*)`, physical `B0`, window 15 and terminal
fields remain open.
-/

namespace YangMills.RG

noncomputable section

/-- At `alpha = 0`, a stabilized endpoint is independent of the Holder
displacement.  Every reciprocal-alias endpoint phase remains untouched. -/
theorem cmp89Eq251ComplexStabilizedEndpointIntegrand_zero_holder_independent
    {d L j : ℕ} {mass a : ℝ} (z : Fin d → ℂ) (mu : Fin d)
    (holder₁ holder₂ endpoint : Fin d → ℝ) :
    cmp89Eq251ComplexStabilizedEndpointIntegrand d L j mass a 0 z mu
        holder₁ endpoint =
      cmp89Eq251ComplexStabilizedEndpointIntegrand d L j mass a 0 z mu
        holder₂ endpoint := by
  unfold cmp89Eq251ComplexStabilizedEndpointIntegrand
    cmp89Eq251ComplexStabilizedEndpointNumerator
    cmp89Eq251ComplexBareEndpointNumerator
  simp

/-- Literal Fourier integrand for one left-derivative endpoint at the physical
fine displacement `xi*endpointU`.  No unit-lattice phase identification is
used. -/
def cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
    (L j : ℕ) [NeZero L] (mass a : ℝ) (z : Fin 4 → ℂ) (mu : Fin 4)
    (endpointU : Fin 4 → ℤ) : ℂ :=
  cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a 0 z mu
    (fun _ => 0)
    (cmp89Eq249PhysicalFineLatticeDisplacement
      (cmp89Eq249FineLatticeSpacing L j) endpointU)

/-- Every physical fine endpoint at `alpha = 0` is exactly the fine Fourier
left-derivative kernel integrand. -/
theorem cmp89Eq251ComplexStabilizedEndpointIntegrand_zero_eq_fineFourierLeftDerivative
    {L j : ℕ} [NeZero L] {mass a : ℝ} (z : Fin 4 → ℂ) (mu : Fin 4)
    (holderU endpointU : Fin 4 → ℤ) :
    cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a 0 z mu
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) holderU)
        (cmp89Eq249PhysicalFineLatticeDisplacement
          (cmp89Eq249FineLatticeSpacing L j) endpointU) =
      cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
        L j mass a z mu endpointU := by
  unfold cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
  exact cmp89Eq251ComplexStabilizedEndpointIntegrand_zero_holder_independent
    z mu _ _ _

/-- Source-normalized fine-lattice Fourier realization of one left-derivative
Green endpoint.  It remains a Fourier definition until the operator dictionary
is proved. -/
def cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel
    (L j : ℕ) [NeZero L] (mass a : ℝ) (mu : Fin 4)
    (endpointU : Fin 4 → ℤ) : ℂ :=
  cmp89Eq249NormalizedFourDimensionalBrillouinIntegral fun x =>
    cmp89Eq249FineLatticeStabilizedFourierLeftDerivativeKernelIntegrand
      L j mass a
      (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
      mu endpointU

/-- The normalized physical fine endpoint is exactly its internally
constructed fine Fourier kernel. -/
theorem cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral_eq_fourierLeftDerivative
    {L j : ℕ} [NeZero L] {mass a : ℝ} (mu : Fin 4)
    (holderU endpointU : Fin 4 → ℤ) :
    cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral
        L j mass a mu holderU endpointU =
      cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel
        L j mass a mu endpointU := by
  unfold cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral
    cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel
  congr 1
  funext x
  exact
    cmp89Eq251ComplexStabilizedEndpointIntegrand_zero_eq_fineFourierLeftDerivative
      (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
      mu holderU endpointU

/-- Literal source-shaped conclusion: the complete normalized physical
fine-lattice expression is the difference of two fine Fourier left-derivative
kernel values.  The two contour signs are still produced independently. -/
theorem cmp89Eq249NormalizedFineLatticeStabilizedIntegral_eq_fourierLeftDerivativeDiff
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
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
  have hfull :=
    cmp89Eq249NormalizedFineLatticeStabilizedIntegral_eq_sub_signedEndpoints
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hmassPos hrho hamplitude hradius hwindow hmass
      mu holderU transportU
  have hfirstShift :=
    cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral_eq_signedEndpoint
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hmassPos hrho hamplitude hradius hwindow hmass
      mu holderU firstU
  have hsecondShift :=
    cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral_eq_signedEndpoint
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hmassPos hrho hamplitude hradius hwindow hmass
      mu holderU transportU
  have hfirstKernel :=
    cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral_eq_fourierLeftDerivative
      (L := L) (j := j) (mass := mass) (a := a)
      mu holderU firstU
  have hsecondKernel :=
    cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral_eq_fourierLeftDerivative
      (L := L) (j := j) (mass := mass) (a := a)
      mu holderU transportU
  calc
    cmp89Eq249NormalizedFineLatticeStabilizedIntegral
        L j mass a mu holderU transportU =
      cmp89Eq249NormalizedFineLatticeStabilizedSignedEndpointIntegral
          L j mass a rho mu holderU firstU -
        cmp89Eq249NormalizedFineLatticeStabilizedSignedEndpointIntegral
          L j mass a rho mu holderU transportU := by
        simpa [firstU] using hfull
    _ = cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral
          L j mass a mu holderU firstU -
        cmp89Eq249NormalizedFineLatticeStabilizedEndpointIntegral
          L j mass a mu holderU transportU :=
      congrArg₂ (fun x y : ℂ => x - y) hfirstShift.symm hsecondShift.symm
    _ = cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel
          L j mass a mu firstU -
        cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel
          L j mass a mu transportU :=
      congrArg₂ (fun x y : ℂ => x - y) hfirstKernel hsecondKernel
    _ = cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel
          L j mass a mu (fun nu => holderU nu + transportU nu) -
        cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel
          L j mass a mu transportU := by
      rfl

end

end YangMills.RG
