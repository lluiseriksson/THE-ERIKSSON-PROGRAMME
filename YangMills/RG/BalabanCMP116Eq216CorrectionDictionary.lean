/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116InteractingResolventCorrection

/-!
# CMP116 equation (2.16): exact correction dictionary

Pages 15--16 of CMP116 replace the contour-dependent operators in the
fluctuation integral by their real base values.  This module fixes the signs
of the three correction operators by exact identities:

* `R₁ = Γ₁† C₁ Γ₁ - Γ₀† C₀ Γ₀` (new minus base);
* `R₂ = K₀ - K₁` (base minus new), because the Gaussian density is written
  with the factor `exp (+ 1/2 <B, R₂ B>)`;
* `R₃ = Γ₁ - Γ₀` (new minus base).

The first correction is expanded into the three exact telescope terms that
must later be estimated using the source difference and the covariance
correction.  The second correction is instantiated for the complete physical
Wilson-plus-gauge precision and receives an exponential kernel bound directly
from the already proved weighted defect estimate.

Honest scope: the physical `R₂` endpoint below compares two real certified
small backgrounds.  It does not yet include the complex contour deformation
of CMP116, construct the physical source difference `R₃`, or prove the full
common estimate (2.16) for all three corrections.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {d N Nc : ℕ} [NeZero N]

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ] PhysicalGaugeOneCochain d N Nc

/-- CMP116 `R₁`, oriented as the new source quadratic form minus the base
source quadratic form. -/
def cmp116R1Correction
    (Γ₀ Γ₁ C₀ C₁ : PhysicalEndomorphism d N Nc) :
    PhysicalEndomorphism d N Nc :=
  Γ₁.adjoint.comp (C₁.comp Γ₁) -
    Γ₀.adjoint.comp (C₀.comp Γ₀)

/-- CMP116 `R₂`, oriented as base precision minus new precision.  This is the
orientation forced by the paper's positive exponential
`exp (+ 1/2 <B, R₂ B>)` in the Gaussian change of measure. -/
def cmp116R2Correction
    (K₀ K₁ : PhysicalEndomorphism d N Nc) :
    PhysicalEndomorphism d N Nc :=
  K₀ - K₁

/-- CMP116 `R₃`, oriented as the new bilinear source minus the base source. -/
def cmp116R3Correction
    (Γ₀ Γ₁ : PhysicalEndomorphism d N Nc) :
    PhysicalEndomorphism d N Nc :=
  Γ₁ - Γ₀

/-- Exact orientation of the quadratic correction on a test field. -/
theorem cmp116R1Correction_apply
    (Γ₀ Γ₁ C₀ C₁ : PhysicalEndomorphism d N Nc)
    (x : PhysicalGaugeOneCochain d N Nc) :
    cmp116R1Correction Γ₀ Γ₁ C₀ C₁ x =
      Γ₁.adjoint (C₁ (Γ₁ x)) -
        Γ₀.adjoint (C₀ (Γ₀ x)) := by
  rfl

/-- Exact orientation of the precision correction on a test field. -/
theorem cmp116R2Correction_apply
    (K₀ K₁ : PhysicalEndomorphism d N Nc)
    (x : PhysicalGaugeOneCochain d N Nc) :
    cmp116R2Correction K₀ K₁ x = K₀ x - K₁ x := by
  rfl

/-- Exact orientation of the bilinear-source correction on a test field. -/
theorem cmp116R3Correction_apply
    (Γ₀ Γ₁ : PhysicalEndomorphism d N Nc)
    (x : PhysicalGaugeOneCochain d N Nc) :
    cmp116R3Correction Γ₀ Γ₁ x = Γ₁ x - Γ₀ x := by
  rfl

/-- Three-term telescope for `R₁`.  The individual summands need not be
self-adjoint; their sum is exactly the difference of the two source quadratic
operators. -/
theorem cmp116R1Correction_eq_telescope
    (Γ₀ Γ₁ C₀ C₁ : PhysicalEndomorphism d N Nc) :
    cmp116R1Correction Γ₀ Γ₁ C₀ C₁ =
      (Γ₁ - Γ₀).adjoint.comp (C₁.comp Γ₁) +
        Γ₀.adjoint.comp ((C₁ - C₀).comp Γ₁) +
        Γ₀.adjoint.comp (C₀.comp (Γ₁ - Γ₀)) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [cmp116R1Correction, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    map_sub]
  abel

/-- Operator-norm form of the exact `R₁` telescope.  It separates the three
analytic debts: the source difference on the left, the covariance difference,
and the source difference on the right. -/
theorem norm_cmp116R1Correction_le
    (Γ₀ Γ₁ C₀ C₁ : PhysicalEndomorphism d N Nc) :
    ‖cmp116R1Correction Γ₀ Γ₁ C₀ C₁‖ ≤
      ‖Γ₁ - Γ₀‖ * ‖C₁‖ * ‖Γ₁‖ +
        ‖Γ₀‖ * ‖C₁ - C₀‖ * ‖Γ₁‖ +
        ‖Γ₀‖ * ‖C₀‖ * ‖Γ₁ - Γ₀‖ := by
  rw [cmp116R1Correction_eq_telescope]
  calc
    ‖(Γ₁ - Γ₀).adjoint.comp (C₁.comp Γ₁) +
          Γ₀.adjoint.comp ((C₁ - C₀).comp Γ₁) +
          Γ₀.adjoint.comp (C₀.comp (Γ₁ - Γ₀))‖
        ≤
          ‖(Γ₁ - Γ₀).adjoint.comp (C₁.comp Γ₁) +
            Γ₀.adjoint.comp ((C₁ - C₀).comp Γ₁)‖ +
          ‖Γ₀.adjoint.comp (C₀.comp (Γ₁ - Γ₀))‖ :=
      norm_add_le _ _
    _
        ≤
          ‖(Γ₁ - Γ₀).adjoint.comp (C₁.comp Γ₁)‖ +
            ‖Γ₀.adjoint.comp ((C₁ - C₀).comp Γ₁)‖ +
            ‖Γ₀.adjoint.comp (C₀.comp (Γ₁ - Γ₀))‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤
          (‖(Γ₁ - Γ₀).adjoint‖ * (‖C₁‖ * ‖Γ₁‖)) +
            (‖Γ₀.adjoint‖ * (‖C₁ - C₀‖ * ‖Γ₁‖)) +
            (‖Γ₀.adjoint‖ * (‖C₀‖ * ‖Γ₁ - Γ₀‖)) := by
      gcongr
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.opNorm_comp_le _ _)
            (norm_nonneg _))
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.opNorm_comp_le _ _)
            (norm_nonneg _))
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.opNorm_comp_le _ _)
            (norm_nonneg _))
    _ =
          ‖Γ₁ - Γ₀‖ * ‖C₁‖ * ‖Γ₁‖ +
            ‖Γ₀‖ * ‖C₁ - C₀‖ * ‖Γ₁‖ +
            ‖Γ₀‖ * ‖C₀‖ * ‖Γ₁ - Γ₀‖ := by
      rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
      ring

variable {L N' : ℕ}
  [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc] [NeZero (L * N')]

/-- The complete physical realization of CMP116 `R₂` between two small
backgrounds. -/
def cmp116InteractingPhysicalR2Correction
    (U₀ U₁ : PhysicalGaugeBackground d (L * N') Nc)
    (a : ℝ) :
    FinePhysicalOneCochain d L N' Nc →L[ℝ]
      FinePhysicalOneCochain d L N' Nc :=
  cmp116R2Correction
    (interactingPhysicalBasePrecisionCLM U₀ a)
    (interactingPhysicalBasePrecisionCLM U₁ a)

/-- The physical `R₂` is literally the difference of the two complete
precisions, with the source-prescribed base-minus-new orientation. -/
theorem cmp116InteractingPhysicalR2Correction_eq
    (U₀ U₁ : PhysicalGaugeBackground d (L * N') Nc)
    (a : ℝ) :
    cmp116InteractingPhysicalR2Correction U₀ U₁ a =
      interactingPhysicalBasePrecisionCLM U₀ a -
        interactingPhysicalBasePrecisionCLM U₁ a := by
  rfl

/-- **Physical `R₂` checkpoint.**  For two certified small Wilson
backgrounds, the exact CMP116 precision correction has an exponentially
decaying kernel with a volume-cardinality-free amplitude. -/
theorem cmp116InteractingPhysicalR2Correction_exponentialKernelBound
    (U₀ U₁ : PhysicalGaugeBackground d (L * N') Nc)
    (a : ℝ)
    {ε₀ ε₁ θ : ℝ}
    (hε₀ : 0 ≤ ε₀) (hε₁ : 0 ≤ ε₁)
    (hsmall₀ : PhysicalWilsonSmallBackground U₀ ε₀)
    (hsmall₁ : PhysicalWilsonSmallBackground U₁ ε₁)
    (hθ : 0 < θ) :
    PhysicalCovarianceExponentialKernelBound
      (cmp116InteractingPhysicalR2Correction U₀ U₁ a)
      physicalBondDist
      (cmp116InteractingTiltedDefectBudget d Nc ε₀ θ +
        cmp116InteractingTiltedDefectBudget d Nc ε₁ θ)
      θ := by
  rw [cmp116InteractingPhysicalR2Correction_eq]
  apply physicalCovarianceExponentialKernelBound_of_tilted_opNorm
    physicalBondDist physicalBondDist_comm physicalBondDist_self
    hθ
    (add_nonneg
      (cmp116InteractingTiltedDefectBudget_nonneg hε₀)
      (cmp116InteractingTiltedDefectBudget_nonneg hε₁))
  intro root
  exact norm_interactingPhysicalBasePrecision_sub_tilt_le
    U₀ U₁ a hε₀ hε₁ hsmall₀ hsmall₁ hθ.le root

end

end YangMills.RG
