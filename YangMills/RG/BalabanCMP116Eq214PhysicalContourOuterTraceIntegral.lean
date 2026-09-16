/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214PhysicalContourDensity
import YangMills.RG.BalabanCMP116ComplexOuterTracePowers

/-!
# Integrated outer contour weight from trace tests

The complex `R₁` correction is global in the outer Gaussian field.  The
correct interface therefore integrates the full outer weight and controls its
quadratic factor by symmetric trace tests; it does not request a pointwise
finite-carrier energy bound.
-/

namespace YangMills.RG

open Matrix MeasureTheory
open scoped Matrix.Norms.Operator

noncomputable section

namespace CMP116Eq214PhysicalContourDensity

variable {nDelta nY lieDim : ℕ} {Bond Site E : Type*}
  {Psi Phi : Site → Type*} [Fintype Bond] [DecidableEq Bond] [Norm E]

/-- The norm of the literal outer weight factors exactly into its determinant
normalization and the global real Gaussian quadratic integral. -/
theorem integral_norm_outerWeight_eq
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi) :
    (∫ x : CMP116Eq214GaussianCoordinate Bond lieDim,
        ‖C.toLocalFiniteGaussianData.outerWeight sigma tau psi phi x‖
        ∂standardGaussianPi (Bond × Fin lieDim)) =
      ‖C.determinantDensity sigma tau psi phi‖ *
        ∫ x : CMP116Eq214GaussianCoordinate Bond lieDim,
          Real.exp
            ((cmp116Eq214ComplexQuadratic
              (C.r1Matrix sigma tau psi phi) x).re)
          ∂standardGaussianPi (Bond × Fin lieDim) := by
  simp_rw [C.norm_outerWeight_eq]
  rw [integral_const_mul]

variable [Nonempty (Bond × Fin lieDim)]

/-- Determinant control plus symmetric trace tests for the literal `R₁`
matrix bound the fully integrated outer weight.  This is the replacement for
the invalid pointwise `hr1` interface. -/
theorem integral_norm_outerWeight_le_of_determinantDensity_of_trace
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (outerBound : ℝ)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (hdet :
      ‖C.determinantDensity sigma tau psi phi‖ ≤ outerBound)
    (hpos :
      (1 -
        cmp116Eq214ComplexQuadraticSymmetricRealPart
          (C.r1Matrix sigma tau psi phi)).PosDef)
    (hsmall :
      ‖(-cmp116Eq214ComplexQuadraticSymmetricRealPart
          (C.r1Matrix sigma tau psi phi)).map Complex.ofRealHom‖ < 1)
    {L : ℝ} (hL : 0 ≤ L)
    (htrace : ∀ P : Matrix (Bond × Fin lieDim) (Bond × Fin lieDim) ℂ,
      P.transpose = P →
      ‖Matrix.trace (C.r1Matrix sigma tau psi phi * P)‖ ≤ L * ‖P‖) :
    (∫ x : CMP116Eq214GaussianCoordinate Bond lieDim,
        ‖C.toLocalFiniteGaussianData.outerWeight sigma tau psi phi x‖
        ∂standardGaussianPi (Bond × Fin lieDim)) ≤
      outerBound *
        Real.exp
          ((L /
            (1 -
              ‖(-cmp116Eq214ComplexQuadraticSymmetricRealPart
                (C.r1Matrix sigma tau psi phi)).map
                  Complex.ofRealHom‖)) / 2) := by
  rw [C.integral_norm_outerWeight_eq]
  have hgauss :=
    integral_exp_re_complexQuadratic_standardGaussianPi_le_of_multiplier
      (C.r1Matrix sigma tau psi phi) hpos hsmall hL htrace
  have houter0 : 0 ≤ outerBound := (norm_nonneg _).trans hdet
  exact mul_le_mul hdet hgauss (by positivity) houter0

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
