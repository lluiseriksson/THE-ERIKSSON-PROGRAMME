/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq216PhysicalR1Decay

/-!
# Common physical kernel certificate for CMP116 equation (2.16)

The three correction operators in CMP116 must be controlled with one decay
rate and one volume-independent amplitude before the Schur estimates of
equation (2.21) can be applied.  This module performs that normalization
without hiding any constant: the common rate is the minimum of the three
rates and the common amplitude is their sum.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {d N Nc : ℕ} [NeZero N]

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- Increasing the kernel amplitude preserves an exponential bound. -/
theorem physicalCovarianceExponentialKernelBound_mono_amplitude
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    {A B κ : ℝ}
    (C : PhysicalEndomorphism d N Nc)
    (hAB : A ≤ B)
    (hC : PhysicalCovarianceExponentialKernelBound C dist A κ) :
    PhysicalCovarianceExponentialKernelBound C dist B κ := by
  refine ⟨hC.1.trans hAB, hC.2.1, ?_⟩
  intro source target v
  exact (hC.2.2 source target v).trans <| by
    gcongr

/-- A literal common-rate, common-amplitude realization of CMP116 (2.16). -/
structure CMP116Eq216PhysicalKernelCertificate
    (R₁ R₂ R₃ : PhysicalEndomorphism d N Nc)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) where
  amplitude : ℝ
  rate : ℝ
  amplitude_nonneg : 0 ≤ amplitude
  rate_pos : 0 < rate
  r1_bound :
    PhysicalCovarianceExponentialKernelBound R₁ dist amplitude rate
  r2_bound :
    PhysicalCovarianceExponentialKernelBound R₂ dist amplitude rate
  r3_bound :
    PhysicalCovarianceExponentialKernelBound R₃ dist amplitude rate

/-- Normalize three independently proved physical kernel estimates to the
single amplitude and single decay rate required by equation (2.16). -/
noncomputable def CMP116Eq216PhysicalKernelCertificate.of_bounds
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (R₁ R₂ R₃ : PhysicalEndomorphism d N Nc)
    {A₁ A₂ A₃ κ₁ κ₂ κ₃ : ℝ}
    (h₁ : PhysicalCovarianceExponentialKernelBound R₁ dist A₁ κ₁)
    (h₂ : PhysicalCovarianceExponentialKernelBound R₂ dist A₂ κ₂)
    (h₃ : PhysicalCovarianceExponentialKernelBound R₃ dist A₃ κ₃) :
    CMP116Eq216PhysicalKernelCertificate R₁ R₂ R₃ dist := by
  let κ := min κ₁ (min κ₂ κ₃)
  let A := A₁ + A₂ + A₃
  have hκ : 0 < κ := by
    dsimp [κ]
    exact lt_min h₁.2.1 (lt_min h₂.2.1 h₃.2.1)
  have hκ₁ : κ ≤ κ₁ := by
    dsimp [κ]
    exact min_le_left _ _
  have hκ₂ : κ ≤ κ₂ := by
    dsimp [κ]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hκ₃ : κ ≤ κ₃ := by
    dsimp [κ]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg (add_nonneg h₁.1 h₂.1) h₃.1
  refine
    { amplitude := A
      rate := κ
      amplitude_nonneg := hA
      rate_pos := hκ
      r1_bound := ?_
      r2_bound := ?_
      r3_bound := ?_ }
  · exact physicalCovarianceExponentialKernelBound_mono_amplitude
      dist (A := A₁) (B := A) R₁
      (by dsimp [A]; linarith [h₂.1, h₃.1])
      (physicalCovarianceExponentialKernelBound_mono_rate
        dist hκ hκ₁ R₁ h₁)
  · exact physicalCovarianceExponentialKernelBound_mono_amplitude
      dist (A := A₂) (B := A) R₂
      (by dsimp [A]; linarith [h₁.1, h₃.1])
      (physicalCovarianceExponentialKernelBound_mono_rate
        dist hκ hκ₂ R₂ h₂)
  · exact physicalCovarianceExponentialKernelBound_mono_amplitude
      dist (A := A₃) (B := A) R₃
      (by dsimp [A]; linarith [h₁.1, h₂.1])
      (physicalCovarianceExponentialKernelBound_mono_rate
        dist hκ hκ₃ R₃ h₃)

/-- Assemble the literal interacting CMP116 corrections into one (2.16)
certificate.  The `R₂` estimate is generated from the two physical small
backgrounds; only the already-derived `R₁` and `R₃` bounds are supplied. -/
noncomputable def
    CMP116Eq216PhysicalKernelCertificate.of_interactingCorrections
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc] [NeZero (L * N')]
    (U₀ U₁ : PhysicalGaugeBackground d (L * N') Nc)
    (a : ℝ)
    (S₀ S₁ C₀ C₁ :
      FinePhysicalOneCochain d L N' Nc →L[ℝ]
        FinePhysicalOneCochain d L N' Nc)
    (complement : Finset (PhysicalBond d (L * N')))
    {A₁ A₃ κ₁ κ₃ ε₀ ε₁ θ : ℝ}
    (hε₀ : 0 ≤ ε₀)
    (hε₁ : 0 ≤ ε₁)
    (hsmall₀ : PhysicalWilsonSmallBackground U₀ ε₀)
    (hsmall₁ : PhysicalWilsonSmallBackground U₁ ε₁)
    (hθ : 0 < θ)
    (hR₁ : PhysicalCovarianceExponentialKernelBound
      (cmp116R1Correction
        (cmp116InteractingPhysicalGammaOperator U₀ a S₀ complement)
        (cmp116InteractingPhysicalGammaOperator U₁ a S₁ complement)
        C₀ C₁)
      physicalBondDist A₁ κ₁)
    (hR₃ : PhysicalCovarianceExponentialKernelBound
      (cmp116InteractingPhysicalR3Correction
        U₀ U₁ a S₀ S₁ complement)
      physicalBondDist A₃ κ₃) :
    CMP116Eq216PhysicalKernelCertificate
      (cmp116R1Correction
        (cmp116InteractingPhysicalGammaOperator U₀ a S₀ complement)
        (cmp116InteractingPhysicalGammaOperator U₁ a S₁ complement)
        C₀ C₁)
      (cmp116InteractingPhysicalR2Correction U₀ U₁ a)
      (cmp116InteractingPhysicalR3Correction
        U₀ U₁ a S₀ S₁ complement)
      physicalBondDist := by
  exact CMP116Eq216PhysicalKernelCertificate.of_bounds
    physicalBondDist
    (cmp116R1Correction
      (cmp116InteractingPhysicalGammaOperator U₀ a S₀ complement)
      (cmp116InteractingPhysicalGammaOperator U₁ a S₁ complement)
      C₀ C₁)
    (cmp116InteractingPhysicalR2Correction U₀ U₁ a)
    (cmp116InteractingPhysicalR3Correction
      U₀ U₁ a S₀ S₁ complement)
    hR₁
    (cmp116InteractingPhysicalR2Correction_exponentialKernelBound
      U₀ U₁ a hε₀ hε₁ hsmall₀ hsmall₁ hθ)
    hR₃

end

end YangMills.RG
