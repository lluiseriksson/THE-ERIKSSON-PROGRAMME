/- Copyright (c) 2026 Lluis Eriksson.
SPDX-License-Identifier: AGPL-3.0-or-later -/

import Mathlib

/-!
# The Amos bound, defined once, and its consumer calculus

The Amos-type upper bound on the modified-Bessel ratio
`I_{ν+1}(x)/I_ν(x) < x / (ν + 1/2 + √((ν+1/2)² + x²))`
is carried in this programme as a named hypothesis at three sites,
previously as textual copies verified against different toolchains.
This module states it ONCE (`amosRHS`, `AmosBound`) and re-proves the
calibration engine and every consumer through the single definition,
inside the pinned mother core.

Sources ported (both originally standalone against Lean 4.30.0-rc2 /
Mathlib cd3b69ba; both `import Mathlib` only, no `sorry`):
- `surface-theorem/PhiMonotone.lean` (untouched Part-I artifact),
- `lean-transfer-matrix/FHBessel/FHBesselAmos.lean`.
The Amos bound itself remains a classical cited theorem (Amos 1974;
Segura 2011; Ruiz-Antolín–Segura 2016); it is NOT proved here.
-/

namespace AmosClosure

/-- Right-hand side of the Amos-type bound at order `ν` and argument
`x`: `x / (ν + 1/2 + √((ν+1/2)² + x²))`. -/
noncomputable def amosRHS (nu x : ℝ) : ℝ :=
  x / (nu + 1/2 + Real.sqrt ((nu + 1/2) ^ 2 + x ^ 2))

/-- The Amos-type bound as a predicate on a candidate ratio `r`. -/
def AmosBound (nu x r : ℝ) : Prop := r < amosRHS nu x

theorem amosBound_iff (nu x r : ℝ) :
    AmosBound nu x r ↔
      r < x / (nu + 1/2 + Real.sqrt ((nu + 1/2) ^ 2 + x ^ 2)) :=
  Iff.rfl

/-- **Calibration engine** (generic in `a`): if
`0 < t < b/(a + √(a²+b²))` then `2a/b < 1/t − t`.  The content is the
exact identity `1/U − U = 2a/b` at `U = b/(a+√(a²+b²)) = (s−a)/b`. -/
theorem amos_calibration (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t)
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

/-- The Amos bound forces smallness: `r < x/(2ν+1)`. -/
theorem amos_small (nu x r : ℝ) (hnu : 0 ≤ nu) (hx : 0 < x) (_hr : 0 < r)
    (hAmos : AmosBound nu x r) :
    r < x / (2 * nu + 1) := by
  rw [amosBound_iff] at hAmos
  set a := nu + 1/2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  set s := Real.sqrt (a ^ 2 + x ^ 2) with hs_def
  have hs2 : s ^ 2 = a ^ 2 + x ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsa : a < s := by nlinarith
  have h2a : 2 * nu + 1 = 2 * a := by rw [ha_def]; ring
  have hlt : x / (a + s) < x / (2 * a) := by
    apply div_lt_div_of_pos_left hx (by linarith) (by linarith)
  rw [h2a]
  exact lt_trans hAmos hlt

/-- **The φ unit step, reduced form** (surface-track consumer).  With
`u` a candidate for `ρ_m = I_{m+1}(b)/I_m(b)`, the Amos bound at order
`m` forces the strict positivity of the reduced quadratic form, by the
exact factorization
`δ = (u + 1/u − 3/b)((1/u − u) − (2m+1)/b) + (2m+1)/b²`. -/
theorem phi_unit_step (m b u : ℝ) (hm : 1 ≤ m) (hb : 0 < b) (hu : 0 < u)
    (hAmos : AmosBound m b u) :
    0 < (1/u^2 - u^2) - (2/b) * ((m-1)*u + (m+2)/u) + 4*(2*m+1)/b^2 := by
  rw [amosBound_iff] at hAmos
  have ha : 0 < m + 1/2 := by linarith
  have hP : 2 * (m + 1/2) / b < 1 / u - u :=
    amos_calibration (m + 1/2) b u ha hb hu hAmos
  have hP' : (2*m+1)/b < 1/u - u := by
    have : 2 * (m + 1/2) / b = (2*m+1)/b := by ring
    linarith [hP, this.symm.le]
  have hsmall : u < b / (2*m+1) :=
    amos_small m b u (by linarith) hb hu (by rw [amosBound_iff]; exact hAmos)
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
  have hkey : (1/u^2 - u^2) - (2/b) * ((m-1)*u + (m+2)/u) + 4*(2*m+1)/b^2
      = (u + 1/u - 3/b) * ((1/u - u) - (2*m+1)/b) + (2*m+1)/b^2 := by
    field_simp
    ring
  rw [hkey]
  have hprod : 0 < (u + 1/u - 3/b) * ((1/u - u) - (2*m+1)/b) :=
    mul_pos hS (by linarith)
  have hlast : 0 < (2*m+1)/b^2 := by positivity
  linarith

/-- **The φ-monotonicity step** (surface-track consumer): with the two
three-term recurrences as hypotheses and the Amos bound at order `m`,
`φ_m < φ_{m+1}` where `φ_m = ((m−1)/R0² + (m+1)R1²)/m`. -/
theorem phi_step_of_recurrences (m b R0 R1 R2 : ℝ)
    (hm : 1 ≤ m) (hb : 0 < b)
    (_hR0 : 0 < R0) (hR1 : 0 < R1)
    (hrec1 : 1 / R0 = R1 + 2 * m / b)
    (hrec2 : R2 = 1 / R1 - 2 * (m+1) / b)
    (hAmos : AmosBound m b R1) :
    ((m-1)/R0^2 + (m+1)*R1^2) / m < (m/R1^2 + (m+2)*R2^2) / (m+1) := by
  have hδ := phi_unit_step m b R1 hm hb hR1 hAmos
  rw [div_lt_div_iff₀ (by linarith : (0:ℝ) < m) (by linarith : (0:ℝ) < m+1)]
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

/-- **The unit step** (Feynman–Hellmann consumer): the three-term
recurrence at order `ν+1` and the Amos bound at order `ν` force
`ρ_ν − ρ_{ν+1} < 1/x` by ordered-field algebra alone (positivity of
`I2` not needed). -/
theorem unit_step_of_recurrence_and_amos
    (x nu I0 I1 I2 : ℝ) (hx : 0 < x) (hnu : 0 ≤ nu)
    (hI0 : 0 < I0) (hI1 : 0 < I1)
    (hrec : I0 - I2 = 2 * (nu + 1) / x * I1)
    (hamos : AmosBound nu x (I1 / I0)) :
    I1 / I0 - I2 / I1 < 1 / x := by
  rw [amosBound_iff] at hamos
  have ha : 0 < nu + 1 / 2 := by linarith
  have ht : 0 < I1 / I0 := div_pos hI1 hI0
  have hcal := amos_calibration (nu + 1 / 2) x (I1 / I0) ha hx ht hamos
  rw [one_div_div] at hcal
  have h2 : I0 / I1 - I2 / I1 = 2 * (nu + 1) / x := by
    rw [div_sub_div_same, hrec, mul_div_cancel_right₀ _ (ne_of_gt hI1)]
  have hsplit : 2 * (nu + 1) / x = 2 * (nu + 1 / 2) / x + 1 / x := by ring
  linarith [hcal, h2, hsplit]

/-- Unit-step increase of the logarithmic derivative in the closed
form `(log I_ν)' = ρ_ν + ν/x` (Feynman–Hellmann consumer). -/
theorem logderiv_unit_step_increase
    (x nu I0 I1 I2 : ℝ) (hx : 0 < x) (hnu : 0 ≤ nu)
    (hI0 : 0 < I0) (hI1 : 0 < I1)
    (hrec : I0 - I2 = 2 * (nu + 1) / x * I1)
    (hamos : AmosBound nu x (I1 / I0)) :
    0 < (I2 / I1 + (nu + 1) / x) - (I1 / I0 + nu / x) := by
  have h := unit_step_of_recurrence_and_amos x nu I0 I1 I2 hx hnu hI0 hI1
    hrec hamos
  have hsplit : (nu + 1) / x - nu / x = 1 / x := by ring
  linarith [h, hsplit]

end AmosClosure
