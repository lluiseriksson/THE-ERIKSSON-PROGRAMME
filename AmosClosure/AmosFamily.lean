/- Copyright (c) 2026 Lluis Eriksson.
SPDX-License-Identifier: AGPL-3.0-or-later -/

import AmosClosure.AmosBarrierReal

/-!
# The one-parameter Amos-type family (arc C5, phase 1; charter
docs/C5-CHARTER.md + Amendments 1-2)

`B_{ν,c}(x) = x/(ν+c+√((ν+c)²+x²))`: positivity for EVERY real `c`
(the denominator is positive for any real shift), the general-`c`
calibration `1/B_c − B_c = 2(ν+c)/x`, the nullcline identity
`Q(B_c) = ((2c−1)/x)·B_c` with its sign trichotomy in `c`, strict
antitonicity of the family in `c`, and the SUFFICIENCY half of the
classification: every `c ≤ 1/2` is a uniform upper bound, by
monotonicity plus C4's `amosBoundReal_holds` at the boundary case
`c = 1/2`.
-/

namespace AmosClosure

/-- The one-parameter Amos-type family `B_{ν,c}`. -/
noncomputable def amosFamily (ν c x : ℝ) : ℝ :=
  x / (ν + c + Real.sqrt ((ν + c) ^ 2 + x ^ 2))

/-- The denominator is positive for EVERY real shift `ν + c`
(the square root strictly dominates `|ν+c|` when `x > 0`). -/
lemma amosFamily_denom_pos (ν c : ℝ) {x : ℝ} (hx : 0 < x) :
    0 < ν + c + Real.sqrt ((ν + c) ^ 2 + x ^ 2) := by
  set a : ℝ := ν + c with ha_def
  set s := Real.sqrt (a ^ 2 + x ^ 2) with hs_def
  have hs2 : s ^ 2 = a ^ 2 + x ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hprod : (s - a) * (s + a) = x ^ 2 := by nlinarith [hs2]
  nlinarith [hprod, hs0, hx, sq_nonneg x, sq_nonneg (s + a)]

lemma amosFamily_pos (ν c : ℝ) {x : ℝ} (hx : 0 < x) :
    0 < amosFamily ν c x :=
  div_pos hx (amosFamily_denom_pos ν c hx)

/-- At `c = 1/2` the family is C4's Amos right-hand side. -/
lemma amosFamily_half (ν x : ℝ) :
    amosFamily ν (1 / 2) x = amosRHS ν x := rfl

/-- **General-`c` calibration**: `1/B_c − B_c = 2(ν+c)/x` for every
real `c` and `x > 0`. -/
lemma amosFamily_calibration (ν c : ℝ) {x : ℝ} (hx : 0 < x) :
    1 / amosFamily ν c x - amosFamily ν c x = 2 * (ν + c) / x := by
  have hden := amosFamily_denom_pos ν c hx
  unfold amosFamily
  set a : ℝ := ν + c with ha_def
  set s := Real.sqrt (a ^ 2 + x ^ 2) with hs_def
  have hs2 : s ^ 2 = a ^ 2 + x ^ 2 := Real.sq_sqrt (by positivity)
  have hsum : 0 < a + s := by
    have : a + s = a + s := rfl
    simpa [ha_def, hs_def, add_comm] using hden
  have hUalt : x / (a + s) = (s - a) / x := by
    rw [div_eq_div_iff (ne_of_gt hsum) (ne_of_gt hx)]
    nlinarith [hs2]
  rw [one_div_div, hUalt]
  field_simp
  ring

/-- **The general-`c` nullcline identity** (the heart of the
classification): `Q(B_{ν,c}) = ((2c−1)/x)·B_{ν,c}`. -/
lemma riccatiQReal_amosFamily (ν c : ℝ) {x : ℝ} (hx : 0 < x) :
    riccatiQReal ν x (amosFamily ν c x)
      = (2 * c - 1) / x * amosFamily ν c x := by
  have hB := amosFamily_pos ν c hx
  have hB' : amosFamily ν c x ≠ 0 := ne_of_gt hB
  have hcal := amosFamily_calibration ν c hx
  have h1 : 1 - amosFamily ν c x ^ 2
      = 2 * (ν + c) / x * amosFamily ν c x := by
    have h := congrArg (fun t => t * amosFamily ν c x) hcal
    simp only [sub_mul, one_div, inv_mul_cancel₀ hB'] at h
    nlinarith [h]
  unfold riccatiQReal
  linear_combination h1

/-- Sign trichotomy, `c > 1/2`: the family value is strictly inside
the Riccati-positive region (`Q > 0` there). -/
lemma riccatiQReal_amosFamily_pos (ν : ℝ) {c x : ℝ} (hx : 0 < x)
    (hc : 1 / 2 < c) :
    0 < riccatiQReal ν x (amosFamily ν c x) := by
  rw [riccatiQReal_amosFamily ν c hx]
  exact mul_pos (div_pos (by linarith) hx) (amosFamily_pos ν c hx)

/-- Sign trichotomy, `c < 1/2`. -/
lemma riccatiQReal_amosFamily_neg (ν : ℝ) {c x : ℝ} (hx : 0 < x)
    (hc : c < 1 / 2) :
    riccatiQReal ν x (amosFamily ν c x) < 0 := by
  rw [riccatiQReal_amosFamily ν c hx]
  exact mul_neg_of_neg_of_pos
    (div_neg_of_neg_of_pos (by linarith) hx) (amosFamily_pos ν c hx)

/-- Sign trichotomy, `c = 1/2`: the nullcline (C4's calibration,
recovered from the general identity). -/
lemma riccatiQReal_amosFamily_zero (ν : ℝ) {x : ℝ} (hx : 0 < x) :
    riccatiQReal ν x (amosFamily ν (1 / 2) x) = 0 := by
  rw [riccatiQReal_amosFamily ν (1 / 2) hx]
  norm_num

/-- **Strict antitonicity of the family in `c`** (the uniformity
mechanism of the sufficiency half): `c₁ ≤ c₂ ⟹ B_{c₂} ≤ B_{c₁}`. -/
lemma amosFamily_anti (ν : ℝ) {c₁ c₂ x : ℝ} (hx : 0 < x)
    (hc : c₁ ≤ c₂) :
    amosFamily ν c₂ x ≤ amosFamily ν c₁ x := by
  have hd₁ := amosFamily_denom_pos ν c₁ hx
  have hd₂ := amosFamily_denom_pos ν c₂ hx
  unfold amosFamily
  set a₁ : ℝ := ν + c₁ with ha1_def
  set a₂ : ℝ := ν + c₂ with ha2_def
  set s₁ := Real.sqrt (a₁ ^ 2 + x ^ 2) with hs1_def
  set s₂ := Real.sqrt (a₂ ^ 2 + x ^ 2) with hs2_def
  have hs1sq : s₁ ^ 2 = a₁ ^ 2 + x ^ 2 := Real.sq_sqrt (by positivity)
  have hs2sq : s₂ ^ 2 = a₂ ^ 2 + x ^ 2 := Real.sq_sqrt (by positivity)
  have hs10 : 0 ≤ s₁ := Real.sqrt_nonneg _
  have hs20 : 0 ≤ s₂ := Real.sqrt_nonneg _
  have ha : a₁ ≤ a₂ := by rw [ha1_def, ha2_def]; linarith
  have hd₁' : 0 < a₁ + s₁ := by
    simpa [ha1_def, hs1_def, add_comm] using hd₁
  have hd₂' : 0 < a₂ + s₂ := by
    simpa [ha2_def, hs2_def, add_comm] using hd₂
  -- monotone denominator: a₁ + s₁ ≤ a₂ + s₂
  have hkey : (s₁ - s₂) * (s₁ + s₂) = (a₂ - a₁) * (-(a₁ + a₂)) := by
    nlinarith [hs1sq, hs2sq]
  have hmono : a₁ + s₁ ≤ a₂ + s₂ := by
    rcases le_total s₁ s₂ with h | h
    · linarith
    · have hsum : 0 < s₁ + s₂ := by
        rcases eq_or_lt_of_le (by positivity : (0:ℝ) ≤ s₁ + s₂) with h0 | h0
        · exfalso
          have hz1 : s₁ = 0 := by linarith [hs10, hs20]
          nlinarith [hs1sq, hx, hz1]
        · exact h0
      have hfac : (0:ℝ) ≤ (a₂ - a₁) * ((a₁ + s₁) + (a₂ + s₂)) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [hkey, hfac, hsum]
  rw [div_le_div_iff₀ hd₂ hd₁]
  have := mul_le_mul_of_nonneg_left hmono hx.le
  nlinarith [this]

/-- **SUFFICIENCY half of the classification** (charter target,
low-risk half): every `c ≤ 1/2` gives a uniform upper bound at
every real order, via antitonicity in `c` and C4's theorem at the
boundary case. -/
theorem amosFamily_upper_of_le_half (ν : ℝ) (hν : 0 ≤ ν) {c : ℝ}
    (hc : c ≤ 1 / 2) {x : ℝ} (hx : 0 < x) :
    besselIReal (ν + 1) x / besselIReal ν x < amosFamily ν c x := by
  have h4 : besselIReal (ν + 1) x / besselIReal ν x < amosRHS ν x :=
    amosBoundReal_holds ν hν hx
  calc besselIReal (ν + 1) x / besselIReal ν x
      < amosRHS ν x := h4
    _ = amosFamily ν (1 / 2) x := (amosFamily_half ν x).symm
    _ ≤ amosFamily ν c x := amosFamily_anti ν hx hc

end AmosClosure
