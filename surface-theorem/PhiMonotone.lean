/-
  PhiMonotone.lean — the φ-monotonicity lemma of the BF2 attack
  (Surface Theorem, last asterisk: structural half c_mn < 0).
  Self-contained; includes amos_calibration. No sorry. Only Mathlib.

  Mathematical statement: with ρ_j = I_{j+1}(β)/I_j(β) and
  φ_m = [(m−1)/ρ_{m−1}² + (m+1)ρ_m²]/m  (m ≥ 1, matching A_m/B_m of
  the π-local expansion including the m = 1 edge), the sequence φ_m is
  strictly increasing.  Consequence: c_mn = A_m B_n − A_n B_m < 0 for
  all m < n.  The analytic inputs enter as named hypotheses: the
  three-term recurrences at orders m and m+1, and the Amos-type upper
  bound at order m — exactly the arsenal of FHBesselAmos.lean.
-/
import Mathlib

/-- Calibration lemma (as in FHBesselAmos.lean). -/
theorem amos_calibration' (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t)
    (hU : t < b / (a + Real.sqrt (a ^ 2 + b ^ 2))) :
    2 * a / b < 1 / t - t := by
  set s := Real.sqrt (a ^ 2 + b ^ 2) with hs_def
  have hs2 : s ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsa : a < s := by nlinarith
  have hsum : 0 < a + s := by linarith
  have hUalt : b / (a + s) = (s - a) / b := by
    rw [div_eq_div_iff (ne_of_gt hsum) (ne_of_gt hb)]
    nlinarith
  have hUval : 1 / (b / (a + s)) - b / (a + s) = 2 * a / b := by
    rw [one_div_div, hUalt]; ring
  have hinv : 1 / (b / (a + s)) < 1 / t :=
    one_div_lt_one_div_of_lt ht hU
  linarith [hU, hinv, hUval]

/-- The Amos bound forces `u < b/(2m+1)` (the denominator exceeds `2a`). -/
lemma amos_small (m b u : ℝ) (hm : 1 ≤ m) (hb : 0 < b) (_hu : 0 < u)
    (hAmos : u < b / (m + 1/2 + Real.sqrt ((m + 1/2) ^ 2 + b ^ 2))) :
    u < b / (2 * m + 1) := by
  set a := m + 1/2 with ha_def
  have ha : 0 < a := by simp [ha_def]; linarith
  set s := Real.sqrt (a ^ 2 + b ^ 2) with hs_def
  have hs2 : s ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsa : a < s := by nlinarith
  have h2a : 2 * m + 1 = 2 * a := by rw [ha_def]; ring
  have hlt : b / (a + s) < b / (2 * a) := by
    apply div_lt_div_of_pos_left hb (by linarith) (by linarith)
  rw [h2a]
  exact lt_trans hAmos hlt

/-- **The φ unit step, reduced form.**  With `u = ρ_m`, the quantity
`δ = (1/u² − u²) − (2/b)((m−1)u + (m+2)/u) + 4(2m+1)/b²` is strictly
positive, by the exact factorization
`δ = (u + 1/u − 3/b)((1/u − u) − (2m+1)/b) + (2m+1)/b²`,
whose first factor is positive by the Amos smallness `u < b/(2m+1) ≤ b/3`
and whose second factor is positive by the calibrated Amos bound
(the unit-step inequality of the companion note). -/
theorem phi_unit_step (m b u : ℝ) (hm : 1 ≤ m) (hb : 0 < b) (hu : 0 < u)
    (hAmos : u < b / (m + 1/2 + Real.sqrt ((m + 1/2) ^ 2 + b ^ 2))) :
    0 < (1/u^2 - u^2) - (2/b) * ((m-1)*u + (m+2)/u) + 4*(2*m+1)/b^2 := by
  have ha : 0 < m + 1/2 := by linarith
  -- second factor: P − (2m+1)/b > 0  (calibrated Amos)
  have hP : 2 * (m + 1/2) / b < 1 / u - u :=
    amos_calibration' (m + 1/2) b u ha hb hu hAmos
  have hP' : (2*m+1)/b < 1/u - u := by
    have : 2 * (m + 1/2) / b = (2*m+1)/b := by ring
    linarith [hP, this.symm.le]
  -- first factor: S − 3/b > 0  (Amos smallness)
  have hsmall : u < b / (2*m+1) := amos_small m b u hm hb hu hAmos
  have h2m : (0:ℝ) < 2*m+1 := by linarith
  have hub : u * (2*m+1) < b := by
    calc u * (2*m+1) < (b/(2*m+1)) * (2*m+1) :=
          mul_lt_mul_of_pos_right hsmall h2m
    _ = b := div_mul_cancel₀ b (ne_of_gt h2m)
  have h1u : (2*m+1)/b < 1/u := by
    rw [div_lt_div_iff₀ hb hu]
    nlinarith
  have h3b : 3/b ≤ (2*m+1)/b := by
    gcongr
    linarith
  have hS : 0 < u + 1/u - 3/b := by
    have h0 : 0 < 1/u := by positivity
    linarith
  -- the exact factorization
  have hkey : (1/u^2 - u^2) - (2/b) * ((m-1)*u + (m+2)/u) + 4*(2*m+1)/b^2
      = (u + 1/u - 3/b) * ((1/u - u) - (2*m+1)/b) + (2*m+1)/b^2 := by
    field_simp
    ring
  rw [hkey]
  have hprod : 0 < (u + 1/u - 3/b) * ((1/u - u) - (2*m+1)/b) :=
    mul_pos hS (by linarith)
  have hlast : 0 < (2*m+1)/b^2 := by positivity
  linarith

/-- **The φ-monotonicity step with the recurrences as hypotheses.**
Writing `R0, R1, R2` for `ρ_{m−1}, ρ_m, ρ_{m+1}`, the two three-term
recurrences and the Amos bound at order `m` force
`φ_m < φ_{m+1}` where `φ_m = ((m−1)/R0² + (m+1)R1²)/m`. -/
theorem phi_step_of_recurrences (m b R0 R1 R2 : ℝ)
    (hm : 1 ≤ m) (hb : 0 < b)
    (_hR0 : 0 < R0) (hR1 : 0 < R1)
    (hrec1 : 1 / R0 = R1 + 2 * m / b)
    (hrec2 : R2 = 1 / R1 - 2 * (m+1) / b)
    (hAmos : R1 < b / (m + 1/2 + Real.sqrt ((m + 1/2) ^ 2 + b ^ 2))) :
    ((m-1)/R0^2 + (m+1)*R1^2) / m < (m/R1^2 + (m+2)*R2^2) / (m+1) := by
  have hδ := phi_unit_step m b R1 hm hb hR1 hAmos
  rw [div_lt_div_iff₀ (by linarith : (0:ℝ) < m) (by linarith : (0:ℝ) < m+1)]
  -- the difference is exactly 2m(m+1)·δ  (algebraic identity)
  have hDelta : (m/R1^2 + (m+2)*R2^2) * m
      - ((m-1)/R0^2 + (m+1)*R1^2) * (m+1)
      = 2*m*(m+1) * ((1/R1^2 - R1^2)
        - (2/b) * ((m-1)*R1 + (m+2)/R1) + 4*(2*m+1)/b^2) := by
    have h0' : (m-1)/R0^2 = (m-1) * (1/R0)^2 := by ring
    rw [hrec2, h0', hrec1]
    field_simp
    ring
  have hpos : 0 < 2*m*(m+1) * ((1/R1^2 - R1^2)
      - (2/b) * ((m-1)*R1 + (m+2)/R1) + 4*(2*m+1)/b^2) := by
    apply mul_pos
    · nlinarith
    · exact hδ
  linarith [hDelta, hpos]

#print axioms amos_calibration'
#print axioms amos_small
#print axioms phi_unit_step
#print axioms phi_step_of_recurrences
