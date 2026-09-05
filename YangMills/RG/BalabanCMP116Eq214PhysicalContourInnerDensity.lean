/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214PhysicalContourRealPart

/-!
# CMP116 equation (2.14): literal inner contour density

The `R₂` quadratic, the signed `R₃` source and the interaction potential all
live under the same positive real reference Gaussian.  They must therefore be
estimated together after taking the complex norm, rather than by unrelated
pointwise bounds on the individual analytic slots.

This module performs that exact regrouping and removes the cutoff factors by
their already proved contraction property.  No Gaussian majorant or physical
kernel estimate is assumed or asserted.
-/

namespace YangMills.RG

open Matrix

noncomputable section

namespace CMP116Eq214PhysicalContourDensity

variable {nDelta nY lieDim : ℕ} {Bond Site E : Type*}
  {Psi Phi : Site → Type*} [Fintype Bond] [DecidableEq Bond] [Norm E]

/-- Complex exponent carried by the inner reference Gaussian. -/
def innerCorrectionExponent
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (x b : CMP116Eq214GaussianCoordinate Bond lieDim) : ℂ :=
  -cmp116Eq214ComplexMixed (C.r3Matrix sigma tau psi phi) x b +
    cmp116Eq214ComplexQuadratic (C.r2Matrix sigma tau psi phi) b +
    C.potential sigma tau psi phi b

/-- Real exponent governing the modulus of the inner density. -/
def realInnerCorrectionExponent
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (x b : CMP116Eq214GaussianCoordinate Bond lieDim) : ℝ :=
  -(b ⬝ᵥ (cmp116Eq214RealPartMatrix
      (C.r3Matrix sigma tau psi phi) *ᵥ x)) +
    (1 / 2 : ℝ) *
      (b ⬝ᵥ (cmp116Eq214RealPartMatrix
        (C.r2Matrix sigma tau psi phi) *ᵥ b)) +
    (C.potential sigma tau psi phi b).re

/-- The two analytic slots under the inner Gaussian are one exponential. -/
theorem innerWeight_mul_exp_interactionExponent_eq
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (x b : CMP116Eq214GaussianCoordinate Bond lieDim) :
    let G := C.toLocalFiniteGaussianData
    G.innerWeight sigma tau psi phi x b *
        Complex.exp (G.interactionExponent sigma tau psi phi b) =
      Complex.exp (C.innerCorrectionExponent sigma tau psi phi x b) := by
  dsimp [toLocalFiniteGaussianData]
  rw [← Complex.exp_add]
  congr 1
  simp only [innerCorrectionExponent]
  ring

/-- Exact entrywise-real representation of the inner modulus exponent. -/
theorem innerCorrectionExponent_re_eq_realInnerCorrectionExponent
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (x b : CMP116Eq214GaussianCoordinate Bond lieDim) :
    (C.innerCorrectionExponent sigma tau psi phi x b).re =
      C.realInnerCorrectionExponent sigma tau psi phi x b := by
  simp [innerCorrectionExponent, realInnerCorrectionExponent,
    cmp116Eq214ComplexQuadratic_re, cmp116Eq214ComplexMixed_re]

/-- The literal cutoff integrand is dominated by the exponential of the real
inner correction exponent.  This is an identity-driven reduction, not a
uniform pointwise hypothesis on the bilinear source. -/
theorem norm_innerIntegrand_le_exp_realInnerCorrectionExponent
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (Y0 P : Finset Bond)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (x b : CMP116Eq214GaussianCoordinate Bond lieDim) :
    ‖C.toLocalFiniteGaussianData.toLocalAnalyticData.localInnerIntegrand
        Y0 P sigma tau psi phi x b‖ ≤
      Real.exp (C.realInnerCorrectionExponent sigma tau psi phi x b) := by
  let G := C.toLocalFiniteGaussianData
  let A := G.toLocalAnalyticData
  rw [CMP116Eq214LocalAnalyticData.localInnerIntegrand, norm_mul, norm_mul]
  have hweights :
      ‖A.innerWeight sigma tau psi phi x b‖ *
          ‖Complex.exp (A.interactionExponent sigma tau psi phi b)‖ =
        ‖Complex.exp (C.innerCorrectionExponent sigma tau psi phi x b)‖ := by
    rw [← norm_mul]
    simpa [A, G] using congrArg norm
      (C.innerWeight_mul_exp_interactionExponent_eq
        sigma tau psi phi x b)
  calc
    ‖A.innerWeight sigma tau psi phi x b‖ *
          ‖A.toAnalyticData.cutoffFactor Y0 P b‖ *
          ‖Complex.exp (A.interactionExponent sigma tau psi phi b)‖ =
        (‖A.innerWeight sigma tau psi phi x b‖ *
          ‖Complex.exp (A.interactionExponent sigma tau psi phi b)‖) *
          ‖A.toAnalyticData.cutoffFactor Y0 P b‖ := by ring
    _ = ‖Complex.exp (C.innerCorrectionExponent sigma tau psi phi x b)‖ *
          ‖A.toAnalyticData.cutoffFactor Y0 P b‖ := by
      rw [hweights]
    _ ≤ ‖Complex.exp (C.innerCorrectionExponent sigma tau psi phi x b)‖ * 1 :=
      mul_le_mul_of_nonneg_left (A.toAnalyticData.norm_cutoffFactor_le_one Y0 P b)
        (norm_nonneg _)
    _ = Real.exp (C.realInnerCorrectionExponent sigma tau psi phi x b) := by
      rw [mul_one, Complex.norm_exp,
        C.innerCorrectionExponent_re_eq_realInnerCorrectionExponent]

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
