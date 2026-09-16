/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249CentralStabilizedComplexFloor
import YangMills.RG.BalabanCMP89Eq251ComplexEndpointAmplitudeBound
import YangMills.RG.BalabanCMP89Eq251FineLatticePhasedNoncentralSum

/-!
# Cold-sealed source-faithful fine-lattice endpoint bound below CMP89 (2.49)

Compiler-verified at exact source checkpoint
`902ed1f06b29568a698c9dfac5856656035ca83e` by cold GitHub Actions run
`31333611513`. Restoration and saving of `.lake/build` were skipped. The focal
and audit exited zero, and all four audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

CMP89 (2.49) retains a separate phase for every reciprocal alias when the
endpoint lies in `xi Z^4`.  This module assembles the central branch and the
phase-retaining noncentral sum at the literal left-derivative specialization
`alpha = 0`.  Every alias acquires the same signed-contour decay because the
alias translation is real; no reciprocal-periodicity identification of the
physical endpoint is used.

Honest scope: this is a pointwise Fourier-integrand bound.  It does not perform
the Brillouin integration, prove the Fourier/physical Green dictionary,
construct the complete `B0`, attain window 15, discharge a terminal field or
inhabit a `TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- Explicit fine-lattice endpoint majorant: the central/noncentral amplitude
bound times the already sealed stabilized reciprocal. -/
def cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound
    (a rho : ℝ) : ℝ :=
  cmp89Eq251ComplexEndpointAmplitudeBound rho *
    cmp89Eq249CentralStabilizedComplexReciprocalBound a rho

/-- Exact source decomposition at `alpha=0`, with every noncentral phase kept
inside its reciprocal-alias sum. -/
theorem cmp89Eq251ComplexStabilizedEndpointNumerator_zero_eq_fineLatticePhased
    {L j : ℕ} {mass : ℝ} (z : Fin 4 → ℂ) (mu : Fin 4)
    (holderDisplacement endpointDisplacement : Fin 4 → ℝ) :
    cmp89Eq251ComplexStabilizedEndpointNumerator 4 L j mass 0 z mu
        holderDisplacement endpointDisplacement =
      Complex.exp (Complex.I * cmp89Eq251EntirePhase z endpointDisplacement) *
          cmp89Eq251ComplexCentralEndpointAmplitude L j z mu +
        cmp89Eq249CentralEntireFineSymbol 4 L j mass z *
          cmp89Eq251ComplexFineLatticePhasedNoncentralSum
            L j mass z mu endpointDisplacement := by
  unfold cmp89Eq251ComplexStabilizedEndpointNumerator
    cmp89Eq251ComplexBareEndpointNumerator
    cmp89Eq251ComplexCentralEndpointAmplitude
    cmp89Eq251ComplexFineLatticePhasedNoncentralSum
  rw [cmp89Eq248EntireAliasMomentum_zero]
  simp [div_eq_mul_inv, mul_assoc]

/-- The complete source numerator at `alpha=0` has one exact physical endpoint
decay and the same explicit central/noncentral amplitude majorant. -/
theorem norm_cmp89Eq251ComplexStabilizedEndpointNumerator_zero_signedContour_le
    {L j : ℕ} [NeZero L] {mass rho : ℝ}
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    (holderDisplacement endpointDisplacement : Fin 4 → ℝ)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (mu : Fin 4) :
    ‖cmp89Eq251ComplexStabilizedEndpointNumerator 4 L j mass 0
        (cmp89Eq251SignedContourMomentum rho p endpointDisplacement) mu
        holderDisplacement endpointDisplacement‖ ≤
      Real.exp (-(rho * cmp89Eq251DisplacementL1 endpointDisplacement)) *
        cmp89Eq251ComplexEndpointAmplitudeBound rho := by
  let z : Fin 4 → ℂ :=
    cmp89Eq251SignedContourMomentum rho p endpointDisplacement
  let decay : ℝ :=
    Real.exp (-(rho * cmp89Eq251DisplacementL1 endpointDisplacement))
  have hreal : ∀ nu, (z nu).re = p nu := by
    intro nu
    simp [z]
  have himag : ∀ nu, |(z nu).im| ≤ rho := by
    intro nu
    exact abs_im_cmp89Eq251SignedContourMomentum_le
      hrho p endpointDisplacement nu
  have hdecay : 0 ≤ decay :=
    (Real.exp_pos _).le
  have hphase :
      ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase z
        endpointDisplacement)‖ = decay := by
    simpa [z, decay, cmp89Eq248EntireAliasMomentum_zero] using
      (norm_exp_I_cmp89Eq251EntireAliasPhase_signedContour
        rho p endpointDisplacement (cmp89Eq249ZeroAlias 4))
  have hcentralAmplitude :=
    norm_cmp89Eq251ComplexCentralEndpointAmplitude_le_bound
      (L := L) (j := j) hrho hp hreal himag mu
  have hcentral :
      ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase z
            endpointDisplacement) *
          cmp89Eq251ComplexCentralEndpointAmplitude L j z mu‖ ≤
        decay * cmp89Eq251ComplexCentralEndpointAmplitudeBound rho := by
    rw [norm_mul, hphase]
    exact mul_le_mul_of_nonneg_left hcentralAmplitude hdecay
  have hfine :=
    norm_cmp89Eq249CentralEntireFineSymbol_le_stripUpperBound
      (L := L) (j := j) hmass hrho hp hreal himag
  have hsum :=
    norm_cmp89Eq251ComplexFineLatticePhasedNoncentralSum_signedContour_le
      (L := L) (j := j) (mass := mass) hrho hradius hp
      endpointDisplacement hamplitude mu
  have hfineNonneg :
      0 ≤ cmp89Eq251CentralFineSymbolStripUpperBound rho := by
    rw [cmp89Eq251CentralFineSymbolStripUpperBound,
      cmp89Eq249CentralFineSymbolVerticalBound,
      cmp89Eq249CentralFineSymbolRealBound]
    positivity
  have hnoncentral :
      ‖cmp89Eq249CentralEntireFineSymbol 4 L j mass z *
          cmp89Eq251ComplexFineLatticePhasedNoncentralSum
            L j mass z mu endpointDisplacement‖ ≤
        decay *
          (cmp89Eq251CentralFineSymbolStripUpperBound rho *
            cmp89Eq251ComplexNoncentralEndpointQuotientSumBound rho) := by
    rw [norm_mul]
    have hmul :=
      mul_le_mul hfine hsum (norm_nonneg _) hfineNonneg
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  rw [cmp89Eq251ComplexStabilizedEndpointNumerator_zero_eq_fineLatticePhased]
  calc
    ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase z
          endpointDisplacement) *
        cmp89Eq251ComplexCentralEndpointAmplitude L j z mu +
      cmp89Eq249CentralEntireFineSymbol 4 L j mass z *
        cmp89Eq251ComplexFineLatticePhasedNoncentralSum
          L j mass z mu endpointDisplacement‖ ≤
        ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase z
            endpointDisplacement) *
          cmp89Eq251ComplexCentralEndpointAmplitude L j z mu‖ +
        ‖cmp89Eq249CentralEntireFineSymbol 4 L j mass z *
          cmp89Eq251ComplexFineLatticePhasedNoncentralSum
            L j mass z mu endpointDisplacement‖ := norm_add_le _ _
    _ ≤ decay * cmp89Eq251ComplexCentralEndpointAmplitudeBound rho +
        decay *
          (cmp89Eq251CentralFineSymbolStripUpperBound rho *
            cmp89Eq251ComplexNoncentralEndpointQuotientSumBound rho) :=
      add_le_add hcentral hnoncentral
    _ = decay * cmp89Eq251ComplexEndpointAmplitudeBound rho := by
      rw [cmp89Eq251ComplexEndpointAmplitudeBound]
      ring

/-- Source-faithful pointwise endpoint-integrand bound at `alpha=0`, without
unit-lattice alias-phase cancellation or a unit-edge premise. -/
theorem norm_cmp89Eq251ComplexStabilizedEndpointIntegrand_zero_signedContour_le
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hmassPos : 0 < mass) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    {p : Fin 4 → ℝ} (hp : ∀ mu, |p mu| ≤ Real.pi)
    (mu : Fin 4)
    (holderDisplacement endpointDisplacement : Fin 4 → ℝ) :
    ‖cmp89Eq251ComplexStabilizedEndpointIntegrand 4 L j mass a 0
        (cmp89Eq251SignedContourMomentum rho p endpointDisplacement) mu
        holderDisplacement endpointDisplacement‖ ≤
      Real.exp (-(rho * cmp89Eq251DisplacementL1 endpointDisplacement)) *
        cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound a rho := by
  let z : Fin 4 → ℂ :=
    cmp89Eq251SignedContourMomentum rho p endpointDisplacement
  let decay : ℝ :=
    Real.exp (-(rho * cmp89Eq251DisplacementL1 endpointDisplacement))
  have hreal : ∀ nu, (z nu).re = p nu := by
    intro nu
    simp [z]
  have himag : ∀ nu, |(z nu).im| ≤ rho := by
    intro nu
    exact abs_im_cmp89Eq251SignedContourMomentum_le
      hrho p endpointDisplacement nu
  have hnum :=
    norm_cmp89Eq251ComplexStabilizedEndpointNumerator_zero_signedContour_le
      (L := L) (j := j) (mass := mass) hmass hrho hradius hp
      holderDisplacement endpointDisplacement hamplitude mu
  have hrecip :=
    norm_inv_cmp89Eq249CentralStabilizedAliasDenominator_le
      (L := L) (j := j) (mass := mass) ha hmassPos hrho hradius hmass
      hwindow hp hreal himag hamplitude
  have hdecay : 0 ≤ decay :=
    (Real.exp_pos _).le
  have hampNonneg :
      0 ≤ cmp89Eq251ComplexEndpointAmplitudeBound rho := by
    have hcentral :
        0 ≤ cmp89Eq251ComplexCentralEndpointAmplitudeBound rho := by
      rw [cmp89Eq251ComplexCentralEndpointAmplitudeBound]
      positivity
    have hfine :
        0 ≤ cmp89Eq251CentralFineSymbolStripUpperBound rho := by
      rw [cmp89Eq251CentralFineSymbolStripUpperBound,
        cmp89Eq249CentralFineSymbolVerticalBound,
        cmp89Eq249CentralFineSymbolRealBound]
      positivity
    have hsum :
        0 ≤ cmp89Eq251ComplexNoncentralEndpointQuotientSumBound rho := by
      rw [cmp89Eq251ComplexNoncentralEndpointQuotientSumBound,
        cmp89Eq251ComplexNoncentralEndpointQuotientConstant,
        cmp89Eq251ComplexNoncentralEndpointRadialConstant,
        cmp89Eq245EntireAverageAliasStripConstant]
      positivity
    rw [cmp89Eq251ComplexEndpointAmplitudeBound]
    exact add_nonneg hcentral (mul_nonneg hfine hsum)
  have hnumBoundNonneg :
      0 ≤ decay * cmp89Eq251ComplexEndpointAmplitudeBound rho :=
    mul_nonneg hdecay hampNonneg
  rw [cmp89Eq251ComplexStabilizedEndpointIntegrand, div_eq_mul_inv, norm_mul,
    cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound]
  have hmul := mul_le_mul hnum hrecip (norm_nonneg _) hnumBoundNonneg
  simpa [z, decay, mul_assoc] using hmul

end

end YangMills.RG
