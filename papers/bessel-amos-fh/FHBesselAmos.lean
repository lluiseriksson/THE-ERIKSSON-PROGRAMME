/-
  FHBesselAmos.lean — machine-checked algebraic core of
  "An Elementary Recurrence–Amos Proof of the Unit-Step Order-Monotonicity
   of (log I_nu)', with a Feynman–Hellmann Application to Two-Dimensional
   Lattice Gauge Theory" (L. Eriksson, July 2026).
  Targets 1 and 2 of Section 5. No sorry. Only Mathlib.
-/
import Mathlib

/-- **Target 1 (calibration lemma).**
If `0 < t < b / (a + sqrt (a^2 + b^2))` with `a, b > 0`, then
`2*a/b < 1/t - t`.  The point is the algebraic identity
`1/U - U = 2a/b` for `U = b/(a + sqrt (a^2+b^2))`, i.e. `U = (s-a)/b`
with `s = sqrt (a^2+b^2)`, via `(s-a)*(s+a) = b^2`. -/
theorem amos_calibration (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t)
    (hU : t < b / (a + Real.sqrt (a ^ 2 + b ^ 2))) :
    2 * a / b < 1 / t - t := by
  set s := Real.sqrt (a ^ 2 + b ^ 2) with hs_def
  have hs2 : s ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsa : a < s := by nlinarith
  have hsum : 0 < a + s := by linarith
  -- U rewritten with rationalized denominator: b/(a+s) = (s-a)/b
  have hUalt : b / (a + s) = (s - a) / b := by
    rw [div_eq_div_iff (ne_of_gt hsum) (ne_of_gt hb)]
    nlinarith
  -- the exact calibration: 1/U - U = 2a/b
  have hUval : 1 / (b / (a + s)) - b / (a + s) = 2 * a / b := by
    rw [one_div_div, hUalt]
    ring
  -- strict antitonicity of t ↦ 1/t - t on (0, ∞), applied to t < U
  have hinv : 1 / (b / (a + s)) < 1 / t := by
    apply one_div_lt_one_div_of_lt ht hU
  linarith [hU, hinv, hUval]

/-- **Target 2 (the unit step, recurrences as hypotheses).**
Writing `I0, I1, I2` for `I_nu x, I_{nu+1} x, I_{nu+2} x`, the three-term
recurrence at order `nu+1` (`hrec`) and the Amos-type upper bound at order
`nu` (`hamos`) already force the unit-step inequality
`rho_nu - rho_{nu+1} < 1/x`, purely by ordered-field algebra.
(Positivity of `I2` is not even needed.) -/
theorem unit_step_of_recurrence_and_amos
    (x nu I0 I1 I2 : ℝ) (hx : 0 < x) (hnu : 0 ≤ nu)
    (hI0 : 0 < I0) (hI1 : 0 < I1)
    (hrec : I0 - I2 = 2 * (nu + 1) / x * I1)
    (hamos : I1 / I0 < x / (nu + 1 / 2 + Real.sqrt ((nu + 1 / 2) ^ 2 + x ^ 2))) :
    I1 / I0 - I2 / I1 < 1 / x := by
  have ha : 0 < nu + 1 / 2 := by linarith
  have ht : 0 < I1 / I0 := div_pos hI1 hI0
  have hcal := amos_calibration (nu + 1 / 2) x (I1 / I0) ha hx ht hamos
  rw [one_div_div] at hcal
  -- hcal : 2 * (nu + 1/2) / x < I0 / I1 - I1 / I0
  have h2 : I0 / I1 - I2 / I1 = 2 * (nu + 1) / x := by
    rw [div_sub_div_same, hrec, mul_div_cancel_right₀ _ (ne_of_gt hI1)]
  have hsplit : 2 * (nu + 1) / x = 2 * (nu + 1 / 2) / x + 1 / x := by ring
  linarith [hcal, h2, hsplit]

/-- The unit-step increase of the logarithmic derivative, in the closed form
`(log I_nu)' = rho_nu + nu/x` of Step 1 of the paper: given the same two
hypotheses, `(rho_{nu+1} + (nu+1)/x) - (rho_nu + nu/x) > 0`. -/
theorem logderiv_unit_step_increase
    (x nu I0 I1 I2 : ℝ) (hx : 0 < x) (hnu : 0 ≤ nu)
    (hI0 : 0 < I0) (hI1 : 0 < I1)
    (hrec : I0 - I2 = 2 * (nu + 1) / x * I1)
    (hamos : I1 / I0 < x / (nu + 1 / 2 + Real.sqrt ((nu + 1 / 2) ^ 2 + x ^ 2))) :
    0 < (I2 / I1 + (nu + 1) / x) - (I1 / I0 + nu / x) := by
  have h := unit_step_of_recurrence_and_amos x nu I0 I1 I2 hx hnu hI0 hI1 hrec hamos
  have hsplit : (nu + 1) / x - nu / x = 1 / x := by ring
  linarith [h, hsplit]

#print axioms amos_calibration
#print axioms unit_step_of_recurrence_and_amos
#print axioms logderiv_unit_step_increase
