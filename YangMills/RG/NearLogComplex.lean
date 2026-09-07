/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.NearLog
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# The Mercator coordinate on the complex unit disk

This file identifies the abstract Banach-algebra series `nearLog` with the
principal complex logarithm on the open unit disk around one.  It is the
scalar analytic input for the future continuous-functional-calculus lift to
normal complex matrices.
-/

namespace YangMills.RG

noncomputable section

/-- On the complex open unit disk, the abstract Mercator coordinate is the
principal complex logarithm of `1 + z`. -/
theorem nearLog_complex {z : ℂ} (hz : ‖z‖ < 1) :
    nearLog z = Complex.log (1 + z) := by
  rw [nearLog]
  rw [← (Complex.hasSum_taylorSeries_log hz).tsum_eq]
  apply tsum_congr
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp only [logCoeff, if_neg hn.ne']
    rw [Complex.real_smul]
    push_cast
    ring

/-- The Mercator coordinate changes sign under inversion whenever both the
element and its inverse stay in the principal near-identity chart. -/
theorem nearLog_inv_sub_one_complex {z : ℂ}
    (hz : ‖z - 1‖ < 1) (hzinv : ‖z⁻¹ - 1‖ < 1) :
    nearLog (z⁻¹ - 1) = -nearLog (z - 1) := by
  have hargMem := Complex.arg_one_add_mem_Ioo hz
  rw [show (1 : ℂ) + (z - 1) = z by ring] at hargMem
  have harg : z.arg ≠ Real.pi := by
    intro h
    rw [h] at hargMem
    linarith [Real.pi_pos, hargMem.2]
  rw [nearLog_complex hzinv, nearLog_complex hz]
  rw [show (1 : ℂ) + (z⁻¹ - 1) = z⁻¹ by ring,
    show (1 : ℂ) + (z - 1) = z by ring, Complex.log_inv z harg]

/-- On the complex unit circle, the inverse automatically remains in the
same near-identity Mercator chart. -/
theorem nearLog_inv_sub_one_complex_of_norm_eq_one {z : ℂ}
    (hnorm : ‖z‖ = 1) (hz : ‖z - 1‖ < 1) :
    nearLog (z⁻¹ - 1) = -nearLog (z - 1) := by
  have hzne : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    norm_num at hnorm
  have hrewrite : z⁻¹ - 1 = z⁻¹ * (1 - z) := by
    field_simp
  apply nearLog_inv_sub_one_complex hz
  rw [hrewrite, norm_mul, norm_inv, hnorm, inv_one, one_mul, norm_sub_rev]
  exact hz

/-- Scalar unitary specialization in the exact shape consumed by the CMP99
unitary-background layer. -/
theorem nearLog_unitary_sub_one_eq_neg_complex (D : unitary ℂ)
    (hD : ‖(D : ℂ) - 1‖ < 1) :
    nearLog (((star D : unitary ℂ) : ℂ) - 1) =
      -nearLog ((D : ℂ) - 1) := by
  rw [Unitary.star_eq_inv D, Unitary.coe_inv]
  exact nearLog_inv_sub_one_complex_of_norm_eq_one
    (CStarRing.norm_coe_unitary D) hD

end

end YangMills.RG
