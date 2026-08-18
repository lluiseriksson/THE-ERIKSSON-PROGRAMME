/-
STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

This scratch file isolates the one-coordinate Jacobian used by G23.4.
It proves an equality of interval integrals, so the opposite half-open
boundary conventions are handled by the existing interval-integral API and
are never identified definitionally.

No Green value, Fourier coefficient, `B0`, window-15 attainment or terminal
field is asserted here.
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
PRE-VALIDATION: this module's source is present, its `.olean` has not yet
been materialized, and its result has not yet been verified by the compiler.
-/

namespace YangMills.RG

open MeasureTheory

noncomputable section

/-- The centered coordinate `t in [-1/2,1/2]` with physical momentum
`p = -2*pi*t` is exactly the source-normalized translated Brillouin
coordinate `x in [0,2*pi]` with `p = -pi+x`.

The factor `(2*pi)^-1` is the literal one-coordinate Jacobian. -/
theorem cmp89CenteredBrillouin_affineSlice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) :
    (2 * Real.pi)⁻¹ •
        (∫ x in (0 : ℝ)..2 * Real.pi, f (-Real.pi + x)) =
      ∫ t in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        f (0 - (2 * Real.pi) * t) := by
  have htwoPi : (2 * Real.pi : ℝ) ≠ 0 :=
    ne_of_gt (mul_pos (by norm_num) Real.pi_pos)
  rw [intervalIntegral.integral_comp_add_left]
  rw [intervalIntegral.integral_comp_sub_mul f htwoPi 0]
  congr 2 <;> ring

/-- Complex-valued spelling matching the scalar multiplication appearing in
the literal normalized Brillouin integral. -/
theorem cmp89CenteredBrillouin_affineSlice_complex
    (f : ℝ → ℂ) :
    ((((2 * Real.pi)⁻¹ : ℝ) : ℂ)) *
        (∫ x in (0 : ℝ)..2 * Real.pi, f (-Real.pi + x)) =
      ∫ t in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        f (-(2 * Real.pi) * t) := by
  rw [← Complex.real_smul]
  calc
    ((2 * Real.pi)⁻¹ : ℝ) •
          (∫ x in (0 : ℝ)..2 * Real.pi, f (-Real.pi + x)) =
        ∫ t in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
          f (0 - (2 * Real.pi) * t) :=
      cmp89CenteredBrillouin_affineSlice f
    _ = ∫ t in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
          f (-(2 * Real.pi) * t) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      ring_nf

end

end YangMills.RG
