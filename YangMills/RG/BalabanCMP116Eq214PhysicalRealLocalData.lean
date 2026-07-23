/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214LocalFiniteGaussianData
import YangMills.RG.BalabanCMP116Eq221PhysicalInteractionExponent

/-!
# CMP116 equation (2.14): literal real physical weights

The real interaction exponent has already been split source-faithfully into
the `R₁` outer quadratic, the `R₃` Gaussian source, and the potential plus
`R₂` inner exponent.  Here those three pieces are installed in the actual
finite-Gaussian analytic-data fields, with external fields restricted by type.

The terminal identity proves that the product of the three analytic weights
is exactly the exponential of the physical real interaction exponent.  This
is the real-contour producer; no complex-contour identification is claimed.
-/

namespace YangMills.RG

open Matrix
open scoped RealInnerProductSpace

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- Literal real-contour finite Gaussian data.  The three physical operators
and the localized potential may depend on the restricted external fields, but
cannot inspect those fields outside the declared supports. -/
def cmp116Eq214PhysicalRealLocalData
    {d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (spectatorSupport fluctuationSupport : Finset Site)
    (rootMatrix : Matrix (CMP116CoordIndex d L lieDim)
      (CMP116CoordIndex d L lieDim) ℝ)
    (R₁ R₂ R₃ :
      RestrictedField spectatorSupport Psi →
      RestrictedField fluctuationSupport Phi →
        PhysicalEndomorphism d (M * N') Nc)
    (potential :
      RestrictedField spectatorSupport Psi →
      RestrictedField fluctuationSupport Phi →
        PhysicalGaugeOneCochain d (M * N') Nc → ℝ)
    (Z0 : Finset (FinBox d N'))
    (bondField : CMP116Eq214GaussianCoordinate (Cube d L) lieDim →
      Cube d L → E)
    (threshold : ℝ) :
    CMP116Eq214LocalFiniteGaussianData 0 0
      (Cube d L) Site Psi Phi E lieDim where
  spectatorSupport := spectatorSupport
  fluctuationSupport := fluctuationSupport
  deltaRadius := Fin.elim0
  yRadius := Fin.elim0
  covarianceRoot := fun _ _ => rootMatrix
  outerWeight := fun _ _ psi phi x =>
    Complex.exp
      (Dict.cmp116Eq221PhysicalR1OuterExponent Z0 (R₁ psi phi)
        (WithLp.toLp 2 x) : ℂ)
  innerWeight := fun _ _ psi phi x b =>
    Complex.exp
      (inner ℝ (WithLp.toLp 2 b)
        (Dict.cmp116Eq221PhysicalR3Source Z0 (R₃ psi phi)
          (WithLp.toLp 2 x)) : ℂ)
  bondField := bondField
  threshold := threshold
  interactionExponent := fun _ _ psi phi b =>
    (Dict.cmp116Eq221PhysicalR2InnerExponent Z0 (R₂ psi phi)
      (potential psi phi) (WithLp.toLp 2 b) : ℂ)

/-- The three literal analytic slots reconstruct the complete real physical
interaction exponent exactly. -/
theorem cmp116Eq214PhysicalRealLocalData_weightProduct_eq
    {d M N' Nc L lieDim : ℕ}
    [NeZero d] [NeZero M] [NeZero N'] [NeZero (M * N')]
    [NeZero Nc] [NeZero L] [NeZero lieDim]
    {Site E : Type*} {Psi Phi : Site → Type*} [Norm E]
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (spectatorSupport fluctuationSupport : Finset Site)
    (rootMatrix : Matrix (CMP116CoordIndex d L lieDim)
      (CMP116CoordIndex d L lieDim) ℝ)
    (R₁ R₂ R₃ :
      RestrictedField spectatorSupport Psi →
      RestrictedField fluctuationSupport Phi →
        PhysicalEndomorphism d (M * N') Nc)
    (potential :
      RestrictedField spectatorSupport Psi →
      RestrictedField fluctuationSupport Phi →
        PhysicalGaugeOneCochain d (M * N') Nc → ℝ)
    (Z0 : Finset (FinBox d N'))
    (bondField : CMP116Eq214GaussianCoordinate (Cube d L) lieDim →
      Cube d L → E)
    (threshold : ℝ)
    (psi : RestrictedField spectatorSupport Psi)
    (phi : RestrictedField fluctuationSupport Phi)
    (x b : CMP116Eq214GaussianCoordinate (Cube d L) lieDim) :
    let G := cmp116Eq214PhysicalRealLocalData Dict spectatorSupport
      fluctuationSupport rootMatrix R₁ R₂ R₃ potential Z0 bondField threshold
    G.outerWeight Fin.elim0 Fin.elim0 psi phi x *
        G.innerWeight Fin.elim0 Fin.elim0 psi phi x b *
        Complex.exp (G.interactionExponent Fin.elim0 Fin.elim0 psi phi b) =
      Complex.exp
        (Dict.cmp116Eq221PhysicalRealInteractionExponent Z0
          (R₁ psi phi) (R₂ psi phi) (R₃ psi phi) (potential psi phi)
          (WithLp.toLp 2 x) (WithLp.toLp 2 b) : ℂ) := by
  dsimp [cmp116Eq214PhysicalRealLocalData]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [Dict.cmp116Eq221PhysicalRealInteractionExponent_eq_split]
  push_cast
  ring

end

end YangMills.RG
