/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214PhysicalContourDensity

/-!
# CMP116 equation (2.14): real part of the complex contour density

The modulus of the contour density depends only on the real part of its
analytic bilinear exponent.  Because both Gaussian variables remain real,
that real part is obtained entrywise from the complex correction matrices.

This module proves that conversion exactly.  It introduces no domination
constant and no estimate standing in for equations (2.16), (2.20), or (2.21).
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators

noncomputable section

/-- Entrywise real part of a complex matrix. -/
def cmp116Eq214RealPartMatrix
    {ι κ : Type*} (A : Matrix ι κ ℂ) : Matrix ι κ ℝ :=
  fun i j => (A i j).re

/-- The real part of an analytic quadratic form on a real field is the
ordinary bilinear quadratic form of the entrywise-real matrix. -/
theorem cmp116Eq214ComplexQuadratic_re
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (x : ι → ℝ) :
    (cmp116Eq214ComplexQuadratic A x).re =
      (1 / 2 : ℝ) *
        (x ⬝ᵥ (cmp116Eq214RealPartMatrix A *ᵥ x)) := by
  simp [cmp116Eq214ComplexQuadratic, cmp116Eq214ComplexCoordinate,
    cmp116Eq214RealPartMatrix, dotProduct, Matrix.mulVec, Complex.mul_re]

/-- The analogous exact identity for the mixed `B · R₃ X` form. -/
theorem cmp116Eq214ComplexMixed_re
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (x b : ι → ℝ) :
    (cmp116Eq214ComplexMixed A x b).re =
      b ⬝ᵥ (cmp116Eq214RealPartMatrix A *ᵥ x) := by
  simp [cmp116Eq214ComplexMixed, cmp116Eq214ComplexCoordinate,
    cmp116Eq214RealPartMatrix, dotProduct, Matrix.mulVec, Complex.mul_re]

namespace CMP116Eq214PhysicalContourDensity

variable {nDelta nY lieDim : ℕ} {Bond Site E : Type*}
  {Psi Phi : Site → Type*} [Fintype Bond] [DecidableEq Bond] [Norm E]

/-- Exact real exponent governing the modulus of the complex contour density.
The signs are inherited from the source dictionary: positive `R₁`, positive
`R₂`, and negative mixed `R₃`. -/
def realCorrectionExponent
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (x b : CMP116Eq214GaussianCoordinate Bond lieDim) : ℝ :=
  (1 / 2 : ℝ) *
      (x ⬝ᵥ (cmp116Eq214RealPartMatrix
        (C.r1Matrix sigma tau psi phi) *ᵥ x)) +
    (1 / 2 : ℝ) *
      (b ⬝ᵥ (cmp116Eq214RealPartMatrix
        (C.r2Matrix sigma tau psi phi) *ᵥ b)) -
    (b ⬝ᵥ (cmp116Eq214RealPartMatrix
      (C.r3Matrix sigma tau psi phi) *ᵥ x)) +
    (C.potential sigma tau psi phi b).re

/-- The source complex exponent and the real modulus exponent are literally
the same after taking real parts. -/
theorem correctionExponent_re_eq_realCorrectionExponent
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (x b : CMP116Eq214GaussianCoordinate Bond lieDim) :
    (C.correctionExponent sigma tau psi phi x b).re =
      C.realCorrectionExponent sigma tau psi phi x b := by
  simp [correctionExponent, realCorrectionExponent,
    cmp116Eq214ComplexQuadratic_re, cmp116Eq214ComplexMixed_re]

/-- Final exact modulus formula expressed only through real matrices and real
Gaussian coordinates. -/
theorem norm_weightProduct_eq_realCorrectionExponent
    (C : CMP116Eq214PhysicalContourDensity nDelta nY
      Bond Site Psi Phi E lieDim)
    (sigma : Fin nDelta → ℂ) (tau : Fin nY → ℂ)
    (psi : RestrictedField C.spectatorSupport Psi)
    (phi : RestrictedField C.fluctuationSupport Phi)
    (x b : CMP116Eq214GaussianCoordinate Bond lieDim) :
    let G := C.toLocalFiniteGaussianData
    ‖G.outerWeight sigma tau psi phi x *
        G.innerWeight sigma tau psi phi x b *
        Complex.exp (G.interactionExponent sigma tau psi phi b)‖ =
      ‖C.determinantDensity sigma tau psi phi‖ *
        Real.exp (C.realCorrectionExponent sigma tau psi phi x b) := by
  dsimp only
  rw [C.norm_weightProduct_eq,
    C.correctionExponent_re_eq_realCorrectionExponent]

end CMP116Eq214PhysicalContourDensity

end

end YangMills.RG
