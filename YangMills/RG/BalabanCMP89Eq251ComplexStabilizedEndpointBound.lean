/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249CentralStabilizedComplexFloor
import YangMills.RG.BalabanCMP89Eq251ComplexEndpointAmplitudeBound
import YangMills.RG.BalabanCMP89Eq251SignedContourPhase
import YangMills.RG.BalabanCMP89Eq251UnitLatticeHolderNormalization

/-!
# PRE-VALIDATION: stabilized endpoint bound below CMP89 (2.49)--(2.51)

Source is present, but this module's `.olean` has not yet been materialized
and its declarations have not yet been verified by the compiler.

The exact endpoint factorization, the phase-free amplitude bound and the
stabilized reciprocal bound combine here on the signed endpoint contour.  A
literal unit Holder edge removes the Holder normalization internally.  The
result retains the exact signed lattice `l1` weight; it does not absorb the
later one-link factor `exp rho`.

This is a pointwise endpoint-integrand bound.  It does not perform the
Brillouin-zone integration, construct the complete physical `B0`, transport
to localization owners, attain window 15, discharge rows 23--24 or inhabit a
`TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- Explicit phase-free amplitude times stabilized reciprocal majorant for
one endpoint integrand.  The two factors remain visible in the definition. -/
def cmp89Eq251ComplexStabilizedEndpointAmplitudeBound
    (a rho : ℝ) : ℝ :=
  cmp89Eq251ComplexEndpointAmplitudeBound rho *
    cmp89Eq249CentralStabilizedComplexReciprocalBound a rho

/-- On its own signed contour, the common lattice phase divided by the
literal unit-edge Holder normalization has exactly the signed `l1` weight. -/
theorem norm_cmp89Eq251ComplexEndpointLatticePhaseFactor_signedContour
    {alpha rho : ℝ} (p : Fin 4 → ℝ)
    {holderU endpointU : Fin 4 → ℤ}
    (hholder : CMP89Eq251UnitLatticeBondDisplacement holderU) :
    ‖cmp89Eq251ComplexEndpointLatticePhaseFactor alpha
        (cmp89Eq251SignedContourMomentum rho p
          (cmp89Eq251LatticeDisplacement endpointU))
        holderU endpointU‖ =
      cmp89SignedLatticeL1ExponentialWeight rho endpointU := by
  have hphase :=
    norm_exp_I_cmp89Eq251EntireAliasPhase_signedContour rho p
      (cmp89Eq251LatticeDisplacement endpointU)
      (cmp89Eq249ZeroAlias 4)
  simp only [cmp89Eq248EntireAliasMomentum_zero] at hphase
  rw [cmp89Eq251ComplexEndpointLatticePhaseFactor, norm_div, hphase,
    cmp89Eq251EuclideanNorm_latticeDisplacement_rpow_eq_one_of_unit hholder,
    Complex.norm_real, Real.norm_eq_abs, abs_one, div_one,
    cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs,
    cmp89Eq251DisplacementL1_latticeDisplacement]
  congr 1
  rfl

/-- The complete stabilized endpoint integrand is bounded on its own signed
contour by the exact lattice `l1` decay times the explicit phase-free
amplitude and reciprocal majorant. -/
theorem norm_cmp89Eq251ComplexStabilizedEndpointIntegrand_signedContour_le
    {L j : ℕ} [NeZero L] {mass a alpha rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    (mu : Fin 4) {holderU endpointU : Fin 4 → ℤ}
    (hholder : CMP89Eq251UnitLatticeBondDisplacement holderU) :
    ‖cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a alpha
        (cmp89Eq251SignedContourMomentum rho p
          (cmp89Eq251LatticeDisplacement endpointU)) mu
        (cmp89Eq251LatticeDisplacement holderU)
        (cmp89Eq251LatticeDisplacement endpointU)‖ ≤
      cmp89SignedLatticeL1ExponentialWeight rho endpointU *
        cmp89Eq251ComplexStabilizedEndpointAmplitudeBound a rho := by
  let z : Fin 4 → ℂ :=
    cmp89Eq251SignedContourMomentum rho p
      (cmp89Eq251LatticeDisplacement endpointU)
  have hreal : ∀ nu, (z nu).re = p nu := by
    intro nu
    simp [z]
  have himag : ∀ nu, |(z nu).im| ≤ rho := by
    intro nu
    exact abs_im_cmp89Eq251SignedContourMomentum_le hrho p
      (cmp89Eq251LatticeDisplacement endpointU) nu
  have hphase :
      ‖cmp89Eq251ComplexEndpointLatticePhaseFactor alpha z
          holderU endpointU‖ =
        cmp89SignedLatticeL1ExponentialWeight rho endpointU := by
    simpa [z] using
      (norm_cmp89Eq251ComplexEndpointLatticePhaseFactor_signedContour
        (alpha := alpha) (rho := rho) p hholder)
  have hamp :=
    norm_cmp89Eq251ComplexEndpointAmplitude_le_bound
      (L := L) (j := j) (mass := mass) hmass hrho hradius hp hreal himag
        hamplitude mu
  have hrecip :=
    norm_inv_cmp89Eq249CentralStabilizedAliasDenominator_le
      (L := L) (j := j) (mass := mass) ha hmassPos hrho hradius hmass
        hwindow hp hreal himag hamplitude
  have hampNonneg :
      0 ≤ cmp89Eq251ComplexEndpointAmplitudeBound rho :=
    (norm_nonneg _).trans hamp
  have hweightNonneg :
      0 ≤ cmp89SignedLatticeL1ExponentialWeight rho endpointU := by
    rw [cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs]
    positivity
  have hnum :
      ‖cmp89Eq251ComplexStabilizedEndpointNumerator 4 L j mass alpha z mu
          (cmp89Eq251LatticeDisplacement holderU)
          (cmp89Eq251LatticeDisplacement endpointU)‖ ≤
        cmp89SignedLatticeL1ExponentialWeight rho endpointU *
          cmp89Eq251ComplexEndpointAmplitudeBound rho := by
    rw [cmp89Eq251ComplexStabilizedEndpointNumerator_eq_phaseFactor_mul_amplitude,
      norm_mul, hphase]
    exact mul_le_mul_of_nonneg_left hamp hweightNonneg
  have hnumBoundNonneg :
      0 ≤ cmp89SignedLatticeL1ExponentialWeight rho endpointU *
        cmp89Eq251ComplexEndpointAmplitudeBound rho :=
    mul_nonneg hweightNonneg hampNonneg
  rw [cmp89Eq251ComplexStabilizedEndpointIntegrand, div_eq_mul_inv, norm_mul,
    cmp89Eq251ComplexStabilizedEndpointAmplitudeBound]
  have hmul := mul_le_mul hnum hrecip (norm_nonneg _) hnumBoundNonneg
  simpa [z, mul_assoc] using hmul

end

end YangMills.RG
