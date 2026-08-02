/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import YangMills.OS.SpatialRing
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-!
# A scalar logarithmic-mixture identity for the spatial vacuum comparison

This file isolates one scalar analytic brick.  It does **not** identify the
finite transfer spectrum and proves neither spatial spectral-sector bound.

The theorem `arcosh_circle_log_mixture` is generic in `c`, `B`, and `s`.  Its
physical front door `physical_arcosh_circle_log_mixture` prints the active
hypotheses `0 < β`, `0 ≤ γ`, and `γ < a`; there
`c = cosh (2 * (a - γ))`, so `γ < a` supplies `1 < c`.
-/

namespace YangMills.OS

open Metric Real

/-! ## The finite logarithmic consequence of the root products -/

/--
Taking norms and logarithms of `periodic_antiperiodic_root_products` gives the
strict finite-grid comparison.  The hypotheses `0 < L` and `0 < x < 1` are
active and printed: in the physical application the latter is supplied by the
disordered-region hypothesis `γ < a`.

This theorem is finite algebra.  It does not identify these sums with finite
transfer-matrix vacua and proves neither spatial spectral-sector bound.
-/
theorem periodic_antiperiodic_log_norm_sums_lt {L : ℕ} (hL : 0 < L)
    {ζ η : ℂ} (hζ : IsPrimitiveRoot ζ L) (hη : η ^ L = -1)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (∑ j ∈ Finset.range L, Real.log ‖1 - (x : ℂ) * ζ ^ j‖) <
      ∑ j ∈ Finset.range L, Real.log ‖1 - (x : ℂ) * (ζ ^ j * η)‖ := by
  rcases periodic_antiperiodic_root_products hL hζ hη hx0 hx1 with
    ⟨hperiodic, hantiperiodic, hperiodicPos, hproductsLt⟩
  have hantiperiodicPos : 0 < 1 + x ^ L := lt_trans hperiodicPos hproductsLt
  have hperiodicProdNe :
      (∏ j ∈ Finset.range L, (1 - (x : ℂ) * ζ ^ j)) ≠ 0 := by
    rw [hperiodic]
    exact_mod_cast hperiodicPos.ne'
  have hantiperiodicProdNe :
      (∏ j ∈ Finset.range L, (1 - (x : ℂ) * (ζ ^ j * η))) ≠ 0 := by
    rw [hantiperiodic]
    exact_mod_cast hantiperiodicPos.ne'
  have hperiodicFactorNe : ∀ j ∈ Finset.range L,
      (1 - (x : ℂ) * ζ ^ j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hperiodicProdNe
  have hantiperiodicFactorNe : ∀ j ∈ Finset.range L,
      (1 - (x : ℂ) * (ζ ^ j * η)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hantiperiodicProdNe
  have hperiodicLog :
      (∑ j ∈ Finset.range L, Real.log ‖1 - (x : ℂ) * ζ ^ j‖) =
        Real.log (1 - x ^ L) := by
    rw [← Real.log_prod fun j hj ↦ norm_ne_zero_iff.mpr (hperiodicFactorNe j hj),
      ← Complex.norm_prod, hperiodic, ← Complex.ofReal_pow]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hperiodicPos]
  have hantiperiodicLog :
      (∑ j ∈ Finset.range L, Real.log ‖1 - (x : ℂ) * (ζ ^ j * η)‖) =
        Real.log (1 + x ^ L) := by
    rw [← Real.log_prod fun j hj ↦ norm_ne_zero_iff.mpr (hantiperiodicFactorNe j hj),
      ← Complex.norm_prod, hantiperiodic, ← Complex.ofReal_pow]
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hantiperiodicPos]
  rw [hperiodicLog, hantiperiodicLog]
  exact Real.strictMonoOn_log hperiodicPos hantiperiodicPos hproductsLt

private noncomputable def arcoshRadius (y : ℝ) : ℝ :=
  Real.exp (-Real.arcosh y)

private lemma arcoshRadius_pos (y : ℝ) : 0 < arcoshRadius y := by
  exact Real.exp_pos _

private lemma arcoshRadius_lt_one {y : ℝ} (hy : 1 < y) : arcoshRadius y < 1 := by
  rw [arcoshRadius, Real.exp_lt_one_iff]
  exact neg_lt_zero.mpr (Real.arcosh_pos hy)

private lemma arcosh_eq_inv_add_radius {y : ℝ} (hy : 1 < y) :
    y = ((arcoshRadius y)⁻¹ + arcoshRadius y) / 2 := by
  calc
    y = Real.cosh (Real.arcosh y) := (Real.cosh_arcosh hy.le).symm
    _ = (Real.exp (Real.arcosh y) + Real.exp (-Real.arcosh y)) / 2 := by
      rw [Real.cosh_eq]
    _ = ((arcoshRadius y)⁻¹ + arcoshRadius y) / 2 := by
      simp [arcoshRadius, Real.exp_neg]

private lemma norm_sub_arcoshRadius_sq {y : ℝ} (hy : 1 < y) {z : ℂ}
    (hz : z ∈ sphere (0 : ℂ) 1) :
    ‖z - (arcoshRadius y : ℂ)‖ ^ 2 =
      2 * arcoshRadius y * (y - z.re) := by
  let r := arcoshRadius y
  change ‖z - (r : ℂ)‖ ^ 2 = 2 * r * (y - z.re)
  have hnorm : ‖z‖ = 1 := by
    simpa [mem_sphere_iff_norm] using hz
  have hrpos : 0 < r := by simpa [r] using arcoshRadius_pos y
  have hyrepr : y = (r⁻¹ + r) / 2 := by
    simpa [r] using arcosh_eq_inv_add_radius hy
  have hyrel : 2 * r * y = 1 + r ^ 2 := by
    rw [hyrepr]
    field_simp [hrpos.ne']
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
  simp [Complex.normSq_eq_norm_sq, hnorm, abs_of_pos hrpos]
  nlinarith

private lemma log_arcosh_kernel_eq {y : ℝ} (hy : 1 < y) {z : ℂ}
    (hz : z ∈ sphere (0 : ℂ) 1) :
    Real.log (y - z.re) =
      2 * Real.log ‖z - (arcoshRadius y : ℂ)‖ -
        Real.log (2 * arcoshRadius y) := by
  have hnorm : ‖z‖ = 1 := by
    simpa [mem_sphere_iff_norm] using hz
  have hre : z.re ≤ 1 := by
    simpa [hnorm] using Complex.re_le_norm z
  have hyre : 0 < y - z.re := by linarith
  have hrpos : 0 < arcoshRadius y := arcoshRadius_pos y
  have hfac := norm_sub_arcoshRadius_sq hy hz
  have hnormpos : 0 < ‖z - (arcoshRadius y : ℂ)‖ := by
    have hsquare : 0 < ‖z - (arcoshRadius y : ℂ)‖ ^ 2 := by
      rw [hfac]
      positivity
    nlinarith [norm_nonneg (z - (arcoshRadius y : ℂ))]
  have hquot :
      y - z.re = ‖z - (arcoshRadius y : ℂ)‖ ^ 2 / (2 * arcoshRadius y) := by
    apply (eq_div_iff (mul_ne_zero two_ne_zero (ne_of_gt hrpos))).2
    nlinarith [hfac]
  rw [hquot, Real.log_div (pow_ne_zero 2 hnormpos.ne')
    (mul_ne_zero two_ne_zero hrpos.ne'), Real.log_pow]
  norm_num

private lemma circleIntegrable_log_arcosh_kernel {y : ℝ} (hy : 1 < y) :
    CircleIntegrable (fun z : ℂ ↦ Real.log (y - z.re)) 0 1 := by
  let r := arcoshRadius y
  have hlog : CircleIntegrable (fun z : ℂ ↦ Real.log ‖z - (r : ℂ)‖) 0 1 :=
    circleIntegrable_log_norm_sub_const 1
  have hmul : CircleIntegrable (fun z : ℂ ↦ 2 * Real.log ‖z - (r : ℂ)‖) 0 1 :=
    hlog.const_mul 2
  have hconst : CircleIntegrable (fun _ : ℂ ↦ Real.log (2 * r)) 0 1 :=
    circleIntegrable_const _ _ _
  have heq : Set.EqOn (fun z : ℂ ↦ Real.log (y - z.re)) (fun z : ℂ ↦
      2 * Real.log ‖z - (r : ℂ)‖ - Real.log (2 * r)) (sphere 0 |(1 : ℝ)|) := by
    intro z hz
    exact log_arcosh_kernel_eq hy (by simpa using hz)
  exact (crcleIntegrable_congr heq).2 (hmul.sub hconst)

private lemma circleAverage_log_arcosh_kernel {y : ℝ} (hy : 1 < y) :
    circleAverage (fun z : ℂ ↦ Real.log (y - z.re)) 0 1 =
      Real.arcosh y - Real.log 2 := by
  let r := arcoshRadius y
  have hrpos : 0 < r := arcoshRadius_pos y
  have hrlt : r < 1 := arcoshRadius_lt_one hy
  have hlog : CircleIntegrable (fun z : ℂ ↦ Real.log ‖z - (r : ℂ)‖) 0 1 :=
    circleIntegrable_log_norm_sub_const 1
  have hmul : CircleIntegrable (fun z : ℂ ↦ 2 * Real.log ‖z - (r : ℂ)‖) 0 1 :=
    hlog.const_mul 2
  have hconst : CircleIntegrable (fun _ : ℂ ↦ Real.log (2 * r)) 0 1 :=
    circleIntegrable_const _ _ _
  have havgzero : circleAverage (fun z : ℂ ↦ Real.log ‖z - (r : ℂ)‖) 0 1 = 0 := by
    apply circleAverage_log_norm_sub_const₀
    simpa [abs_of_pos hrpos] using hrlt
  calc
    circleAverage (fun z : ℂ ↦ Real.log (y - z.re)) 0 1 =
        circleAverage (fun z : ℂ ↦
          2 * Real.log ‖z - (r : ℂ)‖ - Real.log (2 * r)) 0 1 := by
      apply circleAverage_congr_sphere
      intro z hz
      exact log_arcosh_kernel_eq hy (by simpa using hz)
    _ = circleAverage (fun z : ℂ ↦ 2 * Real.log ‖z - (r : ℂ)‖) 0 1 -
        circleAverage (fun _ : ℂ ↦ Real.log (2 * r)) 0 1 := by
      rw [circleAverage_fun_sub hmul hconst]
    _ = 2 * circleAverage (fun z : ℂ ↦ Real.log ‖z - (r : ℂ)‖) 0 1 -
        Real.log (2 * r) := by
      rw [circleAverage_const]
      simpa [smul_eq_mul] using
        (circleAverage_fun_smul (a := (2 : ℝ))
          (f := fun z : ℂ ↦ Real.log ‖z - (r : ℂ)‖) (c := (0 : ℂ)) (R := 1))
    _ = -Real.log (2 * r) := by rw [havgzero]; ring
    _ = Real.arcosh y - Real.log 2 := by
      rw [Real.log_mul two_ne_zero hrpos.ne']
      simp [r, arcoshRadius]
      ring

/--
The scalar arcsine Stieltjes/log mixture in angular coordinates.

The hypotheses `1 < c`, `0 < B`, and `0 ≤ s` are active.  The later physical
specialisation must state `γ < a` explicitly in order to supply `1 < c`; this
generic theorem by itself is not a transfer-spectrum or spectral-gap result.
-/
theorem arcosh_circle_log_mixture {c B s : ℝ} (hc : 1 < c) (hB : 0 < B)
    (hs : 0 ≤ s) :
    Real.arcosh (c + B * s) - Real.arcosh c =
      circleAverage (fun z : ℂ ↦ Real.log (1 + B * s / (c - z.re))) 0 1 := by
  have hBs : 0 ≤ B * s := mul_nonneg hB.le hs
  have hcBs : 1 < c + B * s := lt_of_lt_of_le hc (le_add_of_nonneg_right hBs)
  have hci₁ := circleIntegrable_log_arcosh_kernel hcBs
  have hci₀ := circleIntegrable_log_arcosh_kernel hc
  calc
    Real.arcosh (c + B * s) - Real.arcosh c =
        circleAverage (fun z : ℂ ↦ Real.log (c + B * s - z.re)) 0 1 -
          circleAverage (fun z : ℂ ↦ Real.log (c - z.re)) 0 1 := by
      rw [circleAverage_log_arcosh_kernel hcBs, circleAverage_log_arcosh_kernel hc]
      ring
    _ = circleAverage (fun z : ℂ ↦
        Real.log (c + B * s - z.re) - Real.log (c - z.re)) 0 1 := by
      rw [circleAverage_fun_sub hci₁ hci₀]
    _ = circleAverage (fun z : ℂ ↦ Real.log (1 + B * s / (c - z.re))) 0 1 := by
      apply circleAverage_congr_sphere
      intro z hz
      have hnorm : ‖z‖ = 1 := by
        simpa [mem_sphere_iff_norm] using hz
      have hre : z.re ≤ 1 := by
        simpa [hnorm] using Complex.re_le_norm z
      have hden : 0 < c - z.re := by linarith
      have hnum : 0 < c + B * s - z.re := by linarith
      change Real.log (c + B * s - z.re) - Real.log (c - z.re) =
        Real.log (1 + B * s / (c - z.re))
      rw [← Real.log_div hnum.ne' hden.ne']
      congr 1
      field_simp [hden.ne']
      ring

/--
The physical specialisation of `arcosh_circle_log_mixture`.

The active hypotheses `0 < β`, `0 ≤ γ`, and `γ < a` are printed in the
statement, together with the finite-dual-coupling relation
`tanh a = exp (-2β)`.  The scalar identity is stronger than the physical
specialisation, so the `β` data records the physical regime rather than being
needed by the final algebraic substitution.  The endpoint `γ = 0` is handled
directly: there `B = sinh(2a) sinh(2γ)` vanishes, whereas the generic theorem
deliberately assumes `0 < B`.

This remains a scalar analytic identity.  It does not identify either finite
vacuum, compare the two vacuum products, or prove a spectral-sector bound.
-/
theorem physical_arcosh_circle_log_mixture
    {β γ a s : ℝ} (_hβ : 0 < β) (hγ : 0 ≤ γ) (hγa : γ < a)
    (_hdual : Real.tanh a = Real.exp (-2 * β)) (hs : 0 ≤ s) :
    Real.arcosh
          (Real.cosh (2 * (a - γ)) + Real.sinh (2 * a) * Real.sinh (2 * γ) * s) -
        Real.arcosh (Real.cosh (2 * (a - γ))) =
      circleAverage (fun z : ℂ ↦ Real.log
        (1 + Real.sinh (2 * a) * Real.sinh (2 * γ) * s /
          (Real.cosh (2 * (a - γ)) - z.re))) 0 1 := by
  rcases hγ.eq_or_lt with hγzero | hγpos
  · subst γ
    simp [circleAverage_const]
  · apply arcosh_circle_log_mixture
    · rw [Real.one_lt_cosh]
      nlinarith
    · apply mul_pos
      · rw [Real.sinh_pos_iff]
        nlinarith
      · rw [Real.sinh_pos_iff]
        nlinarith
    · exact hs

/-! ## The elementary logarithmic kernel factorisation -/

/--
The angular kernel factors through a point `x` of the open unit interval when
`t = (1 - x)^2 / (2x)`.  All three active scalar conditions are printed as
`0 < t`, `0 < x < 1`, and the denominator-cleared relation
`2 * x * t = (1 - x)^2`.

This is a pointwise identity on the unit circle.  It does not identify a
finite logarithmic sum with a transfer-matrix vacuum and proves neither
spatial spectral-sector bound.
-/
theorem circle_log_kernel_factorization {t x : ℝ} (ht : 0 < t)
    (hx0 : 0 < x) (hx1 : x < 1) (htx : 2 * x * t = (1 - x) ^ 2)
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) :
    1 + (1 - z.re) / t =
      ‖1 - (x : ℂ) * z‖ ^ 2 / (1 - x) ^ 2 := by
  have hnorm : ‖z‖ = 1 := by
    simpa [mem_sphere_iff_norm] using hz
  have hnormSq :
      ‖1 - (x : ℂ) * z‖ ^ 2 =
        (1 - x) ^ 2 + 2 * x * (1 - z.re) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
    simp [Complex.normSq_eq_norm_sq, hnorm, abs_of_pos hx0]
    ring
  rw [hnormSq, ← htx]
  field_simp [ht.ne', hx0.ne', hx1.ne']

/--
Taking logarithms of `circle_log_kernel_factorization` gives the local bridge
from the scalar log-mixture kernel to the finite root-product logarithms.  Its
active hypotheses `0 < t`, `0 < x < 1`, and
`2 * x * t = (1 - x)^2` remain explicit.

This theorem is still pointwise scalar algebra.  No integration, finite
vacuum comparison, spectral classification, or sector estimate is concluded.
-/
theorem circle_log_kernel_eq_log_norm {t x : ℝ} (ht : 0 < t)
    (hx0 : 0 < x) (hx1 : x < 1) (htx : 2 * x * t = (1 - x) ^ 2)
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) :
    Real.log (1 + (1 - z.re) / t) =
      2 * Real.log ‖1 - (x : ℂ) * z‖ - 2 * Real.log (1 - x) := by
  have hnorm : ‖z‖ = 1 := by
    simpa [mem_sphere_iff_norm] using hz
  have hre : z.re ≤ 1 := by
    simpa [hnorm] using Complex.re_le_norm z
  have hkernel : 0 < 1 + (1 - z.re) / t := by
    have hquot : 0 ≤ (1 - z.re) / t :=
      div_nonneg (sub_nonneg.mpr hre) ht.le
    linarith
  have hfac := circle_log_kernel_factorization ht hx0 hx1 htx hz
  have hden : 0 < 1 - x := sub_pos.mpr hx1
  have hquotPos : 0 < ‖1 - (x : ℂ) * z‖ ^ 2 / (1 - x) ^ 2 := by
    rw [← hfac]
    exact hkernel
  have hnormSq : 0 < ‖1 - (x : ℂ) * z‖ ^ 2 := by
    exact (div_pos_iff_of_pos_right (sq_pos_of_pos hden)).mp hquotPos
  have hnormPos : 0 < ‖1 - (x : ℂ) * z‖ := by
    nlinarith [norm_nonneg (1 - (x : ℂ) * z)]
  rw [hfac, Real.log_div (pow_ne_zero 2 hnormPos.ne')
    (pow_ne_zero 2 hden.ne'), Real.log_pow, Real.log_pow]
  norm_num

end YangMills.OS
