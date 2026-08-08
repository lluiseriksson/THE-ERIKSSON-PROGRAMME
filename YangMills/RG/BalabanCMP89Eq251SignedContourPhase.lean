/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Data.Sign.Basic
import YangMills.RG.BalabanCMP89Eq251ComplexContourPhase

/-!
# Signed endpoint contour momentum below CMP89 (2.51)

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the compiler.

After the physical phase product has been split into its two endpoint phases,
each endpoint may be assigned its own signed imaginary momentum.  This module
constructs that momentum and proves the exact exponential phase decay.  The
reciprocal alias remains real and therefore does not change the decay.

This is not yet a contour-deformation theorem.  In particular it does not
identify integrals on the real and shifted contours, bound the complete
stabilized integrand, construct `B0`, or attain window 15.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Real momentum shifted in the signed imaginary direction selected by one
physical endpoint displacement. -/
def cmp89Eq251SignedContourMomentum {d : ℕ}
    (rho : ℝ) (p displacement : Fin d → ℝ) : Fin d → ℂ :=
  fun mu => (p mu : ℂ) +
    Complex.I *
      ((rho * (SignType.sign (displacement mu) : ℝ) : ℝ) : ℂ)

@[simp]
theorem cmp89Eq251SignedContourMomentum_re
    {d : ℕ} (rho : ℝ) (p displacement : Fin d → ℝ) (mu : Fin d) :
    (cmp89Eq251SignedContourMomentum rho p displacement mu).re = p mu := by
  simp [cmp89Eq251SignedContourMomentum]

@[simp]
theorem cmp89Eq251SignedContourMomentum_im
    {d : ℕ} (rho : ℝ) (p displacement : Fin d → ℝ) (mu : Fin d) :
    (cmp89Eq251SignedContourMomentum rho p displacement mu).im =
      rho * (SignType.sign (displacement mu) : ℝ) := by
  simp [cmp89Eq251SignedContourMomentum]

/-- For nonnegative radius, the signed momentum lies in the closed coordinate
strip of width `rho`. -/
theorem abs_im_cmp89Eq251SignedContourMomentum_le
    {d : ℕ} {rho : ℝ} (hrho : 0 ≤ rho)
    (p displacement : Fin d → ℝ) (mu : Fin d) :
    |(cmp89Eq251SignedContourMomentum rho p displacement mu).im| ≤ rho := by
  have hsign : |(SignType.sign (displacement mu) : ℝ)| ≤ 1 := by
    rw [sign_apply]
    split_ifs <;> norm_num
  rw [cmp89Eq251SignedContourMomentum_im, abs_mul, abs_of_nonneg hrho]
  simpa using mul_le_mul_of_nonneg_left hsign hrho

/-- The imaginary part of the aliased endpoint phase is exactly the radius
times the coordinate `ell^1` displacement. -/
theorem cmp89Eq251EntireAliasPhase_signedContour_im
    {d : ℕ} (rho : ℝ) (p displacement : Fin d → ℝ)
    (m : Fin d → ℤ) :
    (cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum
          (cmp89Eq251SignedContourMomentum rho p displacement) m)
        displacement).im =
      rho * cmp89Eq251DisplacementL1 displacement := by
  rw [cmp89Eq251EntireAliasPhase_im, cmp89Eq251DisplacementL1,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mu _
  rw [cmp89Eq251SignedContourMomentum_im, mul_assoc, sign_mul_self]

/-- Exact alias-independent decay of one endpoint phase on its signed
contour. -/
theorem norm_exp_I_cmp89Eq251EntireAliasPhase_signedContour
    {d : ℕ} (rho : ℝ) (p displacement : Fin d → ℝ)
    (m : Fin d → ℤ) :
    ‖Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum
          (cmp89Eq251SignedContourMomentum rho p displacement) m)
        displacement)‖ =
      Real.exp (-(rho * cmp89Eq251DisplacementL1 displacement)) := by
  rw [norm_exp_I_cmp89Eq251EntireAliasPhase]
  have hphase :=
    cmp89Eq251EntireAliasPhase_signedContour_im rho p displacement m
  rw [cmp89Eq251EntireAliasPhase_im] at hphase
  rw [hphase]

end

end YangMills.RG
