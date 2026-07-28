/- Copyright (c) 2026 Lluis Eriksson.
SPDX-License-Identifier: AGPL-3.0-or-later -/

import AmosClosure.AmosFamily

/-!
# The lower bound by recurrence, and the classification
(arc C5, phase 2; charter Amendments 1-2)

The RS16-type lower bound
`L_ν(x) = x/(ν+1/2+√((ν+3/2)²+x²))` is a SHORT COROLLARY of C4
(no new zone, no new barrier): the ratio recurrence inverts C4's
upper bound at order `ν+1`, and the algebra `x²/(b+s') = s'−b`
collapses the denominator.  With it, the explicit witness
`x₀(c) = 2/(2c−1)` at `ν = 0` refutes every `c > 1/2`, closing
**THE UNIFORM CLASSIFICATION**: `B_{ν,c}` is a uniform upper bound
over all real orders iff `c ≤ 1/2` (known classically in RS16's
α-family form; here machine-checked, uniform in real order,
with a constructive counterexample).
-/

namespace AmosClosure

/-- Ratio form of the real-order recurrence:
`1/ρ_ν = ρ_{ν+1} + 2(ν+1)/x`. -/
theorem besselIReal_ratio_recurrence (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ}
    (hx : 0 < x) :
    1 / (besselIReal (ν + 1) x / besselIReal ν x)
      = besselIReal (ν + 2) x / besselIReal (ν + 1) x
        + 2 * (ν + 1) / x := by
  have h0 := besselIReal_pos ν hν hx
  have h1 := besselIReal_pos (ν + 1) (by linarith) hx
  have hrec := besselIReal_recurrence ν hν hx
  rw [one_div_div]
  have : besselIReal ν x / besselIReal (ν + 1) x
      - besselIReal (ν + 2) x / besselIReal (ν + 1) x
      = 2 * (ν + 1) / x := by
    rw [div_sub_div_same, hrec, mul_div_cancel_right₀ _ (ne_of_gt h1)]
  linarith [this]

/-- The RS16-type lower barrier
`L_ν(x) = x/(ν+1/2+√((ν+3/2)²+x²))`. -/
noncomputable def amosLower (ν x : ℝ) : ℝ :=
  x / (ν + 1 / 2 + Real.sqrt ((ν + 3 / 2) ^ 2 + x ^ 2))

lemma amosLower_denom_pos (ν : ℝ) (hν : 0 ≤ ν) (x : ℝ) :
    0 < ν + 1 / 2 + Real.sqrt ((ν + 3 / 2) ^ 2 + x ^ 2) := by
  have hs : (0 : ℝ) ≤ Real.sqrt ((ν + 3 / 2) ^ 2 + x ^ 2) :=
    Real.sqrt_nonneg _
  linarith

lemma amosLower_pos (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ} (hx : 0 < x) :
    0 < amosLower ν x :=
  div_pos hx (amosLower_denom_pos ν hν x)

/-- **THE LOWER BOUND, BY RECURRENCE FROM C4** (charter Amendment 1:
the former "hard core" as a short corollary): for every real
`ν ≥ 0` and `x > 0`, `L_ν(x) < ρ_ν(x)`. -/
theorem besselLowerReal_holds (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ}
    (hx : 0 < x) :
    amosLower ν x < besselIReal (ν + 1) x / besselIReal ν x := by
  have hρ : 0 < besselIReal (ν + 1) x / besselIReal ν x :=
    besselRatioReal_pos hν hx
  -- C4 at order ν+1, with the (ν+1)+1/2 = ν+3/2 shape normalized
  have hup : besselIReal (ν + 2) x / besselIReal (ν + 1) x
      < x / (ν + 3 / 2 + Real.sqrt ((ν + 3 / 2) ^ 2 + x ^ 2)) := by
    have h := amosBoundReal_holds (ν + 1) (by linarith) hx
    have hshape : amosRHS (ν + 1) x
        = x / (ν + 3 / 2 + Real.sqrt ((ν + 3 / 2) ^ 2 + x ^ 2)) := by
      unfold amosRHS
      rw [show ν + 1 + 1 / 2 = ν + 3 / 2 by ring]
    rw [show ν + 1 + 1 = ν + 2 by ring] at h
    rw [← hshape]
    exact h
  set b : ℝ := ν + 3 / 2 with hb_def
  set s := Real.sqrt (b ^ 2 + x ^ 2) with hs_def
  have hs2 : s ^ 2 = b ^ 2 + x ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hb0 : (0 : ℝ) < b := by rw [hb_def]; linarith
  have hbs : 0 < b + s := by linarith
  -- the collapse: x/(b+s) = (s−b)/x, so 2(ν+1)/x + x/(b+s) = (ν+1/2+s)/x
  have hUalt : x / (b + s) = (s - b) / x := by
    rw [div_eq_div_iff (ne_of_gt hbs) (ne_of_gt hx)]
    nlinarith [hs2]
  have hrec := besselIReal_ratio_recurrence ν hν hx
  -- 1/ρ < (ν+1/2+s)/x
  have hlt : 1 / (besselIReal (ν + 1) x / besselIReal ν x)
      < (ν + 1 / 2 + s) / x := by
    have hsum : x / (b + s) + 2 * (ν + 1) / x = (ν + 1 / 2 + s) / x := by
      rw [hUalt, ← add_div]
      congr 1
      rw [hb_def]
      ring
    calc 1 / (besselIReal (ν + 1) x / besselIReal ν x)
        = besselIReal (ν + 2) x / besselIReal (ν + 1) x
          + 2 * (ν + 1) / x := hrec
      _ < x / (b + s) + 2 * (ν + 1) / x := by linarith [hup]
      _ = (ν + 1 / 2 + s) / x := hsum
  -- invert (both sides positive)
  have hnum : 0 < ν + 1 / 2 + s := by linarith
  have hden : (0 : ℝ) < (ν + 1 / 2 + s) / x := div_pos hnum hx
  have hfin : x / (ν + 1 / 2 + s)
      < besselIReal (ν + 1) x / besselIReal ν x := by
    rw [div_lt_iff₀ hnum]
    have h1 : 1 < (besselIReal (ν + 1) x / besselIReal ν x)
        * ((ν + 1 / 2 + s) / x) := by
      have := mul_lt_mul_of_pos_left hlt hρ
      rw [mul_one_div, div_self (ne_of_gt hρ)] at this
      linarith [this]
    have h2 := mul_lt_mul_of_pos_left h1 hx
    calc x = x * 1 := by ring
      _ < x * ((besselIReal (ν + 1) x / besselIReal ν x)
          * ((ν + 1 / 2 + s) / x)) := h2
      _ = besselIReal (ν + 1) x / besselIReal ν x
          * (ν + 1 / 2 + s) := by
          field_simp
  unfold amosLower
  rw [← hs_def, ← hb_def] at *
  exact hfin

/-- The explicit witness at `ν = 0` (charter Amendment 1, finding
3): for every `c > 1/2`, at `x₀(c) = 2/(2c−1)` the family member
falls strictly below the lower barrier. -/
lemma amosFamily_lt_amosLower_witness {c : ℝ} (hc : 1 / 2 < c) :
    amosFamily 0 c (2 / (2 * c - 1)) < amosLower 0 (2 / (2 * c - 1)) := by
  have h2c : (0 : ℝ) < 2 * c - 1 := by linarith
  set x : ℝ := 2 / (2 * c - 1) with hx_def
  have hx : 0 < x := by rw [hx_def]; positivity
  have hdB := amosFamily_denom_pos 0 c hx
  have hdL := amosLower_denom_pos 0 le_rfl x
  unfold amosFamily amosLower
  simp only [zero_add]
  -- both have numerator x > 0: B < L ⟺ denom_L < denom_B
  set sB := Real.sqrt (c ^ 2 + x ^ 2) with hsB_def
  set sL := Real.sqrt ((3 / 2 : ℝ) ^ 2 + x ^ 2) with hsL_def
  have hsB2 : sB ^ 2 = c ^ 2 + x ^ 2 := Real.sq_sqrt (by positivity)
  have hsL2 : sL ^ 2 = (3 / 2 : ℝ) ^ 2 + x ^ 2 := Real.sq_sqrt (by positivity)
  have hsB0 : 0 ≤ sB := Real.sqrt_nonneg _
  have hsL0 : 0 ≤ sL := Real.sqrt_nonneg _
  have hkey : 1 / 2 + sL < c + sB := by
    have hsLx : x < sL := by nlinarith [hsL2, hsL0, hx]
    have hsBx : x ≤ sB := by nlinarith [hsB2, hsB0, hx, sq_nonneg c]
    have hprod : (sL - sB) * (sL + sB) = 9 / 4 - c ^ 2 := by
      nlinarith [hsL2, hsB2]
    have h94 : 9 / 4 - c ^ 2 < (2 * c - 1) * x := by
      have hxval : (2 * c - 1) * x = 2 := by
        rw [hx_def]
        field_simp
      rw [hxval]
      nlinarith [hc]
    have hsum : 2 * x < sL + sB := by linarith
    nlinarith [hprod, h94, hsum, mul_pos h2c hx,
      mul_lt_mul_of_pos_left hsum (by linarith : (0:ℝ) < c - 1/2)]
  have hdB' : (0:ℝ) < c + sB := by
    have := amosFamily_denom_pos 0 c hx
    simpa [hsB_def, zero_add] using this
  rw [div_lt_div_iff₀ hdB' (by linarith : (0:ℝ) < 1/2 + sL)]
  nlinarith [hkey, hx]

/-- **THE UNIFORM CLASSIFICATION** (charter target; classically
RS16's α-family statement, machine-checked here, uniform in real
order, with the constructive counterexample): `B_{ν,c}` is a
uniform upper bound for the real-order Bessel ratio over all
`ν ≥ 0`, `x > 0`, if and only if `c ≤ 1/2`. -/
theorem amosFamily_uniform_upper_iff (c : ℝ) :
    (∀ ν : ℝ, 0 ≤ ν → ∀ x : ℝ, 0 < x →
        besselIReal (ν + 1) x / besselIReal ν x < amosFamily ν c x)
      ↔ c ≤ 1 / 2 := by
  constructor
  · intro h
    by_contra hcgt
    push_neg at hcgt
    have h2c : (0 : ℝ) < 2 * c - 1 := by linarith
    have hx : (0 : ℝ) < 2 / (2 * c - 1) := by positivity
    have hup := h 0 le_rfl (2 / (2 * c - 1)) hx
    have hwit := amosFamily_lt_amosLower_witness hcgt
    have hlow := besselLowerReal_holds 0 le_rfl hx
    simp only [zero_add] at hup hlow
    linarith [hup, hwit, hlow]
  · intro hc ν hν x hx
    exact amosFamily_upper_of_le_half ν hν hc hx

end AmosClosure
