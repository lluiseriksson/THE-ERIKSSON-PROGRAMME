/- Copyright (c) 2026 Lluis Eriksson.
SPDX-License-Identifier: AGPL-3.0-or-later -/

import AmosClosure.BesselDeriv

/-!
# The Riccati structure of the Bessel ratio (arc C3, phase 1)

The ratio `ρ_n = besselI (n+1) / besselI n` satisfies the Riccati
equation `ρ' = 1 − ((2n+1)/x)·ρ − ρ²` — a pure consequence of the
quotient rule, the derivative identity, and the recurrence, all
already theorems.  The Amos right-hand side `amosRHS n x` is exactly
the positive root of the Riccati quadratic (the calibration identity
in disguise), which is what makes the barrier proof of arc C3 run.
-/

namespace AmosClosure

/-- The Riccati quadratic at order `n` and argument `x`. -/
noncomputable def riccatiQ (n : ℕ) (x y : ℝ) : ℝ :=
  1 - (2 * n + 1) / x * y - y ^ 2

/-- **The Riccati equation for the Bessel ratio** (phase-1 target,
judge J-C3-1): pure consequence of C2's theorems. -/
theorem besselRatio_hasDerivAt (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => besselI (n + 1) y / besselI n y)
      (riccatiQ n x (besselI (n + 1) x / besselI n x)) x := by
  have hx' : x ≠ 0 := ne_of_gt hx
  have h0 := besselI_pos n hx
  have h0' : besselI n x ≠ 0 := ne_of_gt h0
  have hf := besselI_hasDerivAt (n + 1) hx
  have hg := besselI_hasDerivAt n hx
  have hdiv := hf.div hg h0'
  convert hdiv using 1
  have hrec := besselI_recurrence n hx
  have hI2 : besselI (n + 1 + 1) x
      = besselI n x - 2 * ((n : ℝ) + 1) / x * besselI (n + 1) x := by
    rw [show n + 1 + 1 = n + 2 from rfl]
    linarith [hrec]
  rw [hI2]
  unfold riccatiQ
  push_cast
  field_simp
  ring

/-- Positivity of the Amos right-hand side. -/
lemma amosRHS_pos (n : ℕ) {x : ℝ} (hx : 0 < x) : 0 < amosRHS n x := by
  unfold amosRHS
  have ha : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
  have hs : (0 : ℝ) ≤ Real.sqrt (((n : ℝ) + 1 / 2) ^ 2 + x ^ 2) :=
    Real.sqrt_nonneg _
  positivity

/-- **The calibration identity for the Amos RHS itself**:
`1/B − B = (2n+1)/x` at `B = amosRHS n x`. -/
lemma amosRHS_calibration (n : ℕ) {x : ℝ} (hx : 0 < x) :
    1 / amosRHS n x - amosRHS n x = (2 * n + 1) / x := by
  unfold amosRHS
  set a : ℝ := (n : ℝ) + 1 / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; positivity
  set s := Real.sqrt (a ^ 2 + x ^ 2) with hs_def
  have hs2 : s ^ 2 = a ^ 2 + x ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsa : a < s := by nlinarith
  have hsum : 0 < a + s := by linarith
  have hUalt : x / (a + s) = (s - a) / x := by
    rw [div_eq_div_iff (ne_of_gt hsum) (ne_of_gt hx)]
    nlinarith
  have h2a : 2 * (n : ℝ) + 1 = 2 * a := by rw [ha_def]; ring
  rw [one_div_div, hUalt, h2a]
  field_simp
  ring

/-- The Amos RHS is the root of the Riccati quadratic: `Q(B) = 0`. -/
lemma riccatiQ_amosRHS (n : ℕ) {x : ℝ} (hx : 0 < x) :
    riccatiQ n x (amosRHS n x) = 0 := by
  have hB := amosRHS_pos n hx
  have hB' : amosRHS n x ≠ 0 := ne_of_gt hB
  have hcal := amosRHS_calibration n hx
  unfold riccatiQ
  have h1 : 1 - amosRHS n x ^ 2 = (2 * n + 1) / x * amosRHS n x := by
    have h := congrArg (fun t => t * amosRHS n x) hcal
    simp only [sub_mul, one_div, inv_mul_cancel₀ hB'] at h
    nlinarith [h]
  linarith [h1]

/-- Strict positivity of the quadratic strictly below the root:
`Q(y) > 0` for `0 ≤ y < B`. -/
lemma riccatiQ_pos_of_lt (n : ℕ) {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hyB : y < amosRHS n x) :
    0 < riccatiQ n x y := by
  have hB := amosRHS_pos n hx
  have hQB := riccatiQ_amosRHS n hx
  have hc : (0 : ℝ) ≤ (2 * n + 1) / x := by positivity
  unfold riccatiQ at hQB ⊢
  nlinarith [hQB, hyB, hy, hB, hc]

end AmosClosure
