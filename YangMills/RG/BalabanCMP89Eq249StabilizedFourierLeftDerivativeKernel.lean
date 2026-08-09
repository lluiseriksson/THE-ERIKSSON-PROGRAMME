/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249NormalizedStabilizedIntegralRecombination
import YangMills.RG.BalabanCMP89Eq251ComplexEndpointAmplitudeFactorization

/-!
# PRE-VALIDATION: Fourier realization of the CMP89 left-derivative kernel

Source is present at the checkpoint containing this file; its `.olean` has not
yet been materialized and the result is not yet compiler-verified.

CMP89 (2.49), visually checked on printed page 585, is the normalized Holder
difference of the left derivative of `G_j Q_j^*`.  The already sealed
stabilized integrand has the exact printed Fourier numerator and denominator,
but its endpoint form still carries a Holder displacement and exponent.

This module first defines an alpha-free Fourier kernel integrand from the
literal endpoint phase, the sealed central/noncentral amplitude, and the
stabilized denominator.  A unit lattice edge removes the Holder normalization
and identifies each old endpoint integrand with this kernel integrand.  The
four-dimensional normalized kernel is then constructed internally, and the
existing normalized stabilized integral is proved to be exactly the
difference of its two endpoint kernel values.

Honest scope: this is the Fourier side of (2.49).  It does not identify the
new definition with the repository's generated or regional Green operator,
construct the complete physical `B0`, attain window 15, discharge a terminal
field, or inhabit a `TermSource`.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- Alpha-free endpoint integrand for the Fourier realization of the left
derivative of `G_j Q_j^*` in CMP89 (2.49). -/
def cmp89Eq249StabilizedFourierLeftDerivativeKernelIntegrand
    (L j : ℕ) (mass a : ℝ) (z : Fin 4 → ℂ) (mu : Fin 4)
    (endpointU : Fin 4 → ℤ) : ℂ :=
  Complex.exp (Complex.I * cmp89Eq251EntirePhase z
      (cmp89Eq251LatticeDisplacement endpointU)) *
    cmp89Eq251ComplexEndpointAmplitude L j mass z mu /
      cmp89Eq249CentralStabilizedAliasDenominator 4 L j mass a z

/-- On a literal unit Holder edge, one stabilized endpoint is exactly the
alpha-free Fourier kernel integrand. -/
theorem cmp89Eq251ComplexStabilizedEndpointIntegrand_eq_fourierLeftDerivative
    {L j : ℕ} {mass a alpha : ℝ} (z : Fin 4 → ℂ) (mu : Fin 4)
    (holderU endpointU : Fin 4 → ℤ)
    (hholder : CMP89Eq251UnitLatticeBondDisplacement holderU) :
    cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a alpha z mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement endpointU) =
      cmp89Eq249StabilizedFourierLeftDerivativeKernelIntegrand
        L j mass a z mu endpointU := by
  unfold cmp89Eq251ComplexStabilizedEndpointIntegrand
    cmp89Eq249StabilizedFourierLeftDerivativeKernelIntegrand
  rw [cmp89Eq251ComplexStabilizedEndpointNumerator_eq_phaseFactor_mul_amplitude]
  unfold cmp89Eq251ComplexEndpointLatticePhaseFactor
  rw [cmp89Eq251EuclideanNorm_latticeDisplacement_rpow_eq_one_of_unit hholder]
  simp

/-- Source-normalized Fourier realization of one left-derivative Green
endpoint.  This remains a Fourier definition until the operator dictionary is
proved. -/
def cmp89Eq249NormalizedStabilizedFourierLeftDerivativeKernel
    (L j : ℕ) [NeZero L] (mass a : ℝ) (mu : Fin 4)
    (endpointU : Fin 4 → ℤ) : ℂ :=
  cmp89Eq249NormalizedFourDimensionalBrillouinIntegral fun x =>
    cmp89Eq249StabilizedFourierLeftDerivativeKernelIntegrand
      L j mass a
      (fun nu ↦ (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
      mu endpointU

/-- Contour displacement does not change the normalized Fourier kernel.  The
proof consumes the common full-polydisc hypotheses and the unit-edge
normalization; no endpoint function or equality is accepted as input. -/
theorem cmp89Eq249NormalizedStabilizedFourierLeftDerivativeKernel_eq_signed
    {L j : ℕ} [NeZero L] {mass a alpha rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (holderU endpointU : Fin 4 → ℤ)
    (hholder : CMP89Eq251UnitLatticeBondDisplacement holderU) :
    cmp89Eq249NormalizedStabilizedFourierLeftDerivativeKernel
        L j mass a mu endpointU =
      cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
        (fun x => cmp89Eq251ComplexStabilizedEndpointIntegrand
          4 L j mass a alpha
          (cmp89Eq251SignedContourMomentum rho
            (cmp89Eq251PhysicalBrillouinParameter x)
            (cmp89Eq251LatticeDisplacement endpointU)) mu
          (cmp89Eq251LatticeDisplacement holderU)
          (cmp89Eq251LatticeDisplacement endpointU)) := by
  have hreal :
      (∫ x, cmp89Eq249StabilizedFourierLeftDerivativeKernelIntegrand
          L j mass a
          (fun nu ↦ (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ))
          mu endpointU
        ∂cmp89Eq249FourDimensionalBrillouinMeasure) =
        ∫ x, cmp89Eq251ComplexStabilizedEndpointIntegrand
          4 L j mass a alpha
          (fun nu ↦ (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)) mu
          (cmp89Eq251LatticeDisplacement holderU)
          (cmp89Eq251LatticeDisplacement endpointU)
        ∂cmp89Eq249FourDimensionalBrillouinMeasure := by
    apply integral_congr_ae
    filter_upwards with x
    exact (cmp89Eq251ComplexStabilizedEndpointIntegrand_eq_fourierLeftDerivative
      (fun nu ↦ (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)) mu
      holderU endpointU hholder).symm
  have hcontour :
      (∫ x, cmp89Eq251ComplexStabilizedEndpointIntegrand
          4 L j mass a alpha
          (fun nu ↦ (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)) mu
          (cmp89Eq251LatticeDisplacement holderU)
          (cmp89Eq251LatticeDisplacement endpointU)
        ∂cmp89Eq249FourDimensionalBrillouinMeasure) =
        ∫ x, cmp89Eq251ComplexStabilizedEndpointIntegrand
          4 L j mass a alpha
          (cmp89Eq251SignedContourMomentum rho
            (cmp89Eq251PhysicalBrillouinParameter x)
            (cmp89Eq251LatticeDisplacement endpointU)) mu
          (cmp89Eq251LatticeDisplacement holderU)
          (cmp89Eq251LatticeDisplacement endpointU)
        ∂cmp89Eq249FourDimensionalBrillouinMeasure := by
    simpa [cmp89Eq249FourDimensionalBrillouinMeasure] using
      (integral_cmp89Eq251ComplexStabilizedEndpointIntegrand_eq_signed
        (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
        (rho := rho) ha hmassPos hrho hamplitude hradius hwindow hmass
        mu holderU endpointU)
  unfold cmp89Eq249NormalizedStabilizedFourierLeftDerivativeKernel
    cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
  rw [hreal, hcontour]

/-- Literal source-shaped conclusion: the normalized stabilized expression
is the normalized Holder difference of two internally constructed Fourier
left-derivative kernel values. -/
theorem cmp89Eq249NormalizedStabilizedIntegral_eq_fourierLeftDerivativeDiff
    {L j : ℕ} [NeZero L] {mass a alpha rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (holderU transportU : Fin 4 → ℤ)
    (hholder : CMP89Eq251UnitLatticeBondDisplacement holderU) :
    cmp89Eq249NormalizedFourDimensionalStabilizedIntegral
        L j mass a alpha mu holderU transportU =
      cmp89Eq249NormalizedStabilizedFourierLeftDerivativeKernel
          L j mass a mu (fun nu ↦ holderU nu + transportU nu) -
        cmp89Eq249NormalizedStabilizedFourierLeftDerivativeKernel
          L j mass a mu transportU := by
  rw [cmp89Eq249NormalizedFourDimensionalStabilizedIntegral_eq_sub_endpoints
    (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
    (rho := rho) ha hmassPos hrho hamplitude hradius hwindow hmass
    mu holderU transportU]
  rw [← cmp89Eq249NormalizedStabilizedFourierLeftDerivativeKernel_eq_signed
      (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
      (rho := rho) ha hmassPos hrho hamplitude hradius hwindow hmass
      mu holderU (fun nu ↦ holderU nu + transportU nu) hholder,
    ← cmp89Eq249NormalizedStabilizedFourierLeftDerivativeKernel_eq_signed
      (L := L) (j := j) (mass := mass) (a := a) (alpha := alpha)
      (rho := rho) ha hmassPos hrho hamplitude hradius hwindow hmass
      mu holderU transportU hholder]

end

end YangMills.RG
