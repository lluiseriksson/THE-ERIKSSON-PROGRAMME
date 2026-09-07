/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251NoncentralLaplacianRatio
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Holder phase factor in CMP89 (2.49)--(2.51)

Cold GitHub Actions run `31236522003` compiler-verified source checkpoint
`52ca4c60f2269e322d00531ec89bd7dabbdbb91e` with workflow checkpoint
`adc9893a58e46f63ead8ec0eff87cbb5c39e46dd`. Both restore and save of
`.lake/build` were skipped; the focal and audit exited zero, the build closed
at 3287 jobs, and all five audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

CMP89 printed p. 585 extracts the factor

`|x-x'|^(-alpha) * |exp(i*(p'+l).(x-x')) - 1|`

and bounds it by `O(1) * |p'+l|^alpha` for `0 <= alpha <= 1`.
This module proves that comparison with the source Euclidean norm made
literal as `sqrt (sum_mu q_mu^2)`.  Cauchy--Schwarz controls the phase, while
the elementary global estimate

`|exp(i*t)-1| <= 2 * |t|^alpha`

avoids any small-phase restriction.  Division by the nonzero displacement
norm then gives the explicit constant `2`.  No sup-norm substitution or
dimension factor is hidden in the statement.

This module does not combine the phase factor with the averaging amplitude,
derivative and massive-symbol ratio, and it does not prove the complete
integrand estimate (2.51), the analytic strip, or a regional transport.

Source catalog key: `cmp89.local-green.fourier.2.34-2.51`.
-/

namespace YangMills.RG

noncomputable section

/-- Literal Euclidean norm associated with the momentum square already used
in the massive-symbol comparison. -/
def cmp89Eq251EuclideanNorm {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  Real.sqrt (cmp89Eq251MomentumSquare v)

theorem cmp89Eq251EuclideanNorm_nonneg
    {d : ℕ} (v : Fin d → ℝ) :
    0 ≤ cmp89Eq251EuclideanNorm v := by
  exact Real.sqrt_nonneg _

/-- The real phase `(p'+l).(x-x')` in CMP89 (2.49). -/
def cmp89Eq251Phase {d : ℕ} (q displacement : Fin d → ℝ) : ℝ :=
  ∑ mu, q mu * displacement mu

/-- Euclidean Cauchy--Schwarz for the literal source phase. -/
theorem abs_cmp89Eq251Phase_le
    {d : ℕ} (q displacement : Fin d → ℝ) :
    |cmp89Eq251Phase q displacement| ≤
      cmp89Eq251EuclideanNorm q * cmp89Eq251EuclideanNorm displacement := by
  calc
    |∑ mu, q mu * displacement mu| ≤
        ∑ mu, |q mu * displacement mu| := by
      simpa only [Finset.sum_attach, Finset.mem_univ, true_and] using
        (Finset.abs_sum_le_sum_abs
          (fun mu : Fin d => q mu * displacement mu) Finset.univ)
    _ = ∑ mu, |q mu| * |displacement mu| := by
      apply Finset.sum_congr rfl
      intro mu _
      rw [abs_mul]
    _ ≤ Real.sqrt (∑ mu, |q mu| ^ 2) *
        Real.sqrt (∑ mu, |displacement mu| ^ 2) := by
      simpa using
        (Real.sum_mul_le_sqrt_mul_sqrt
          (Finset.univ : Finset (Fin d))
          (fun mu => |q mu|) (fun mu => |displacement mu|))
    _ = cmp89Eq251EuclideanNorm q *
        cmp89Eq251EuclideanNorm displacement := by
      simp only [cmp89Eq251EuclideanNorm, cmp89Eq251MomentumSquare,
        sq_abs]

/-- Global scalar Holder estimate for a unitary phase.  The constant `2` is
valid without restricting the size of the phase. -/
theorem norm_exp_I_mul_sub_one_le_two_mul_abs_rpow
    {alpha t : ℝ} (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    ‖Complex.exp (Complex.I * t) - 1‖ ≤ 2 * |t| ^ alpha := by
  have hlinear :
      ‖Complex.exp (Complex.I * t) - 1‖ ≤ |t| := by
    simpa [Real.norm_eq_abs] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t))
  have htwo : ‖Complex.exp (Complex.I * t) - 1‖ ≤ 2 := by
    calc
      ‖Complex.exp (Complex.I * t) - 1‖ ≤
          ‖Complex.exp (Complex.I * t)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [Complex.norm_exp_I_mul_ofReal]; norm_num
  by_cases ht : |t| ≤ 1
  · have hpow : |t| ≤ |t| ^ alpha := by
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_ge'
          (abs_nonneg t) ht halpha0 halpha1)
    exact hlinear.trans (by
      nlinarith [Real.rpow_nonneg (abs_nonneg t) alpha])
  · have hone : 1 ≤ |t| := (le_of_lt (lt_of_not_ge ht))
    have hpow : 1 ≤ |t| ^ alpha := Real.one_le_rpow hone halpha0
    exact htwo.trans (by nlinarith)

/-- The source phase factor before division by the displacement Holder
weight. -/
theorem norm_cmp89Eq251_phaseFactor_le
    {d : ℕ} {alpha : ℝ} (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (q displacement : Fin d → ℝ) :
    ‖Complex.exp (Complex.I * cmp89Eq251Phase q displacement) - 1‖ ≤
      2 * (cmp89Eq251EuclideanNorm q ^ alpha *
        cmp89Eq251EuclideanNorm displacement ^ alpha) := by
  have hphase := abs_cmp89Eq251Phase_le q displacement
  have hphasePow :
      |cmp89Eq251Phase q displacement| ^ alpha ≤
        (cmp89Eq251EuclideanNorm q *
          cmp89Eq251EuclideanNorm displacement) ^ alpha :=
    Real.rpow_le_rpow (abs_nonneg _) hphase halpha0
  calc
    ‖Complex.exp (Complex.I * cmp89Eq251Phase q displacement) - 1‖ ≤
        2 * |cmp89Eq251Phase q displacement| ^ alpha :=
      norm_exp_I_mul_sub_one_le_two_mul_abs_rpow halpha0 halpha1
    _ ≤ 2 * (cmp89Eq251EuclideanNorm q *
        cmp89Eq251EuclideanNorm displacement) ^ alpha := by
      gcongr
    _ = 2 * (cmp89Eq251EuclideanNorm q ^ alpha *
        cmp89Eq251EuclideanNorm displacement ^ alpha) := by
      rw [Real.mul_rpow (cmp89Eq251EuclideanNorm_nonneg q)
        (cmp89Eq251EuclideanNorm_nonneg displacement)]

/-- Literal Holder quotient printed between CMP89 (2.49) and (2.51), with
the nonzero displacement condition explicit and the constant `2` visible. -/
theorem norm_cmp89Eq251_phaseFactor_div_displacement_rpow_le
    {d : ℕ} {alpha : ℝ} (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (q displacement : Fin d → ℝ)
    (hdisplacement : 0 < cmp89Eq251EuclideanNorm displacement) :
    ‖Complex.exp (Complex.I * cmp89Eq251Phase q displacement) - 1‖ /
        cmp89Eq251EuclideanNorm displacement ^ alpha ≤
      2 * cmp89Eq251EuclideanNorm q ^ alpha := by
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hdisplacement alpha)).2
  simpa [mul_assoc] using
    norm_cmp89Eq251_phaseFactor_le halpha0 halpha1 q displacement

end

end YangMills.RG
