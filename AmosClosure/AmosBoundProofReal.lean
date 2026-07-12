/- Copyright (c) 2026 Lluis Eriksson.
SPDX-License-Identifier: AGPL-3.0-or-later -/

import AmosClosure.RiccatiReal

/-!
# The zone at real order (arc C4, phase 3b; charter Amendment 4)

`ψ_ν(x) > 2ν+1` on `0 < x ≤ 1/4`, uniformly in `ν ≥ 0`, by the
registered safe route: geometric domination from the PHASE-1 exact
ratio identity (no Γ/rpow redeployment), product-form sum bound,
strictness EXCLUSIVELY from the two-term lower bound, the
initial-term identity derived from the already-proved
`besselRealTerm_rec_zero`, and the uniformity mechanism isolated in
two named lemmas (`(ν+1)/(ν+2) ≤ 1`, never discretization of `ν`).
-/

namespace AmosClosure

/-! ### Series bounds (product form throughout) -/

/-- Termwise geometric domination at real order:
`t_{ν,k} ≤ t_{ν,0}·q^k` with `q = (x/2)²/(ν+1)`, by induction from
the phase-1 exact ratio identity. -/
lemma besselRealTerm_le_geometric (ν : ℝ) (hν : 0 ≤ ν) (k : ℕ) {x : ℝ}
    (hx : 0 < x) :
    besselRealTerm ν k x
      ≤ besselRealTerm ν 0 x * ((x / 2) ^ 2 / (ν + 1)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hstep : besselRealTerm ν (k + 1) x
        ≤ besselRealTerm ν k x * ((x / 2) ^ 2 / (ν + 1)) := by
      rw [besselRealTerm_succ ν hν k hx]
      have hden : (0 : ℝ) < ((k : ℝ) + 1) * (ν + k + 1) := by
        have := gamma_arg_pos ν hν k
        positivity
      have hmono : (ν + 1) ≤ ((k : ℝ) + 1) * (ν + k + 1) := by nlinarith
      have hr : (x / 2) ^ 2 / (((k : ℝ) + 1) * (ν + k + 1))
          ≤ (x / 2) ^ 2 / (ν + 1) := by
        rw [div_le_div_iff₀ hden (by linarith : (0 : ℝ) < ν + 1)]
        have hx2 : (0 : ℝ) ≤ (x / 2) ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hmono hx2]
      exact mul_le_mul_of_nonneg_left hr (besselRealTerm_nonneg ν hν k hx)
    calc besselRealTerm ν (k + 1) x
        ≤ besselRealTerm ν k x * ((x / 2) ^ 2 / (ν + 1)) := hstep
      _ ≤ (besselRealTerm ν 0 x * ((x / 2) ^ 2 / (ν + 1)) ^ k)
          * ((x / 2) ^ 2 / (ν + 1)) := by
          apply mul_le_mul_of_nonneg_right ih
          apply div_nonneg (by positivity) (by linarith)
      _ = besselRealTerm ν 0 x * ((x / 2) ^ 2 / (ν + 1)) ^ (k + 1) := by
          rw [pow_succ]; ring

/-- Geometric upper bound in product form at real order:
`(1−q)·I_ν(x) ≤ t_{ν,0}` when `q = (x/2)²/(ν+1) < 1`. -/
lemma besselIReal_mul_le (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ} (hx : 0 < x)
    (hq : (x / 2) ^ 2 / (ν + 1) < 1) :
    (1 - (x / 2) ^ 2 / (ν + 1)) * besselIReal ν x
      ≤ besselRealTerm ν 0 x := by
  have hq0 : (0 : ℝ) ≤ (x / 2) ^ 2 / (ν + 1) :=
    div_nonneg (by positivity) (by linarith)
  have hgeo : Summable
      (fun k => besselRealTerm ν 0 x * ((x / 2) ^ 2 / (ν + 1)) ^ k) :=
    (summable_geometric_of_lt_one hq0 hq).mul_left _
  have hle := (summable_besselRealTerm ν hν hx).tsum_le_tsum
    (fun k => besselRealTerm_le_geometric ν hν k hx) hgeo
  have hsum : ∑' k, besselRealTerm ν 0 x * ((x / 2) ^ 2 / (ν + 1)) ^ k
      = besselRealTerm ν 0 x * (1 - (x / 2) ^ 2 / (ν + 1))⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq]
  have h1q : (0 : ℝ) < 1 - (x / 2) ^ 2 / (ν + 1) := by linarith
  have hI : besselIReal ν x
      ≤ besselRealTerm ν 0 x * (1 - (x / 2) ^ 2 / (ν + 1))⁻¹ := by
    calc besselIReal ν x
        ≤ ∑' k, besselRealTerm ν 0 x * ((x / 2) ^ 2 / (ν + 1)) ^ k := hle
      _ = _ := hsum
  have h1q' : (1 - (x / 2) ^ 2 / (ν + 1)) ≠ 0 := ne_of_gt h1q
  calc (1 - (x / 2) ^ 2 / (ν + 1)) * besselIReal ν x
      ≤ (1 - (x / 2) ^ 2 / (ν + 1))
        * (besselRealTerm ν 0 x * (1 - (x / 2) ^ 2 / (ν + 1))⁻¹) :=
        mul_le_mul_of_nonneg_left hI h1q.le
    _ = besselRealTerm ν 0 x := by
        rw [mul_comm (besselRealTerm ν 0 x) _, ← mul_assoc,
          mul_inv_cancel₀ h1q', one_mul]

/-- Strict first-term lower bound (THE strictness source of the
whole chain): `t_{ν,0} < I_ν(x)` for `x > 0`, from the two leading
terms. -/
lemma besselRealTerm_zero_lt_besselIReal (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ}
    (hx : 0 < x) :
    besselRealTerm ν 0 x < besselIReal ν x := by
  have hsum := summable_besselRealTerm ν hν hx
  have h2 : ∑ k ∈ Finset.range 2, besselRealTerm ν k x ≤ besselIReal ν x :=
    hsum.sum_le_tsum _ (fun j _ => besselRealTerm_nonneg ν hν j hx)
  have hpos1 : 0 < besselRealTerm ν 1 x := besselRealTerm_pos ν hν 1 hx
  have hexp : ∑ k ∈ Finset.range 2, besselRealTerm ν k x
      = besselRealTerm ν 0 x + besselRealTerm ν 1 x := by
    simp [Finset.sum_range_succ]
  linarith [h2]

/-- Exact first-term ratio identity at real order, DERIVED from the
phase-1 `besselRealTerm_rec_zero` (no Γ/rpow redeployment):
`2(ν+1)·t_{ν+1,0} = x·t_{ν,0}`. -/
lemma besselRealTerm_zero_succ (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ}
    (hx : 0 < x) :
    2 * (ν + 1) * besselRealTerm (ν + 1) 0 x
      = x * besselRealTerm ν 0 x := by
  have h := besselRealTerm_rec_zero ν hν hx
  have hx' : x ≠ 0 := ne_of_gt hx
  field_simp at h
  linear_combination h

/-! ### The uniformity mechanism, isolated and named -/

/-- The whole ν-uniformity of the zone: `(ν+1)/(ν+2) ≤ 1`. -/
lemma real_zone_ratio_uniform (ν : ℝ) (hν : 0 ≤ ν) :
    (ν + 1) / (ν + 2) ≤ 1 := by
  rw [div_le_one (by linarith)]
  linarith

/-- Coefficient inequality on the zone:
`2ν+1+x² ≤ 2(ν+1)·(1 − q_{ν+1})` with `q_{ν+1} = (x/2)²/(ν+2)`,
for `0 < x ≤ 1/4`. -/
lemma real_zone_coefficient_bound (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ}
    (hx : 0 < x) (hx4 : x ≤ 1 / 4) :
    2 * ν + 1 + x ^ 2
      ≤ 2 * (ν + 1) * (1 - (x / 2) ^ 2 / (ν + 2)) := by
  have hr := real_zone_ratio_uniform ν hν
  have hx2 : x ^ 2 ≤ 1 / 16 := by nlinarith
  have h2ne : (ν + 2 : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hq : 2 * (ν + 1) * ((x / 2) ^ 2 / (ν + 2))
      = x ^ 2 / 2 * ((ν + 1) / (ν + 2)) := by
    field_simp
  have hq2 : 2 * (ν + 1) * ((x / 2) ^ 2 / (ν + 2)) ≤ x ^ 2 / 2 := by
    rw [hq]
    have hx20 : (0 : ℝ) ≤ x ^ 2 / 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hr hx20]
  nlinarith [hq2, hx2]

/-! ### The zone theorem -/

/-- **ZONE at real order**: `ψ_ν(x) > 2ν+1` for `0 < x ≤ 1/4`,
uniformly in `ν ≥ 0`; strictness enters ONLY at the last link. -/
theorem besselPsiReal_zone (ν : ℝ) (hν : 0 ≤ ν) {x : ℝ} (hx : 0 < x)
    (hx4 : x ≤ 1 / 4) :
    2 * ν + 1 < besselPsiReal ν x := by
  have hI0 := besselIReal_pos ν hν hx
  have hI1 := besselIReal_pos (ν + 1) (by linarith) hx
  have hx2 : x ^ 2 ≤ 1 / 16 := by nlinarith
  have hq0 : (0 : ℝ) ≤ (x / 2) ^ 2 / (ν + 2) :=
    div_nonneg (by positivity) (by linarith)
  have hqhalf : (x / 2) ^ 2 / (ν + 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < ν + 2)]
    nlinarith
  have hq1 : (x / 2) ^ 2 / (ν + 2) < 1 := by linarith
  -- product-form facts, applied at order ν+1 (the registered SHIFT
  -- RISK site: (ν+1)+1 = ν+2, rewritten explicitly)
  have hup : (1 - (x / 2) ^ 2 / (ν + 2)) * besselIReal (ν + 1) x
      ≤ besselRealTerm (ν + 1) 0 x := by
    have h := besselIReal_mul_le (ν + 1) (by linarith) hx
      (by rw [show ν + 1 + 1 = ν + 2 by ring]; exact hq1)
    rwa [show ν + 1 + 1 = ν + 2 by ring] at h
  have hlo : besselRealTerm ν 0 x < besselIReal ν x :=
    besselRealTerm_zero_lt_besselIReal ν hν hx
  have hid : 2 * (ν + 1) * besselRealTerm (ν + 1) 0 x
      = x * besselRealTerm ν 0 x := besselRealTerm_zero_succ ν hν hx
  have hcoef := real_zone_coefficient_bound ν hν hx hx4
  -- key strict chain: (2ν+1+x²)·I_{ν+1} < x·I_ν
  have hkey : (2 * ν + 1 + x ^ 2) * besselIReal (ν + 1) x
      < x * besselIReal ν x := by
    have s1 : (2 * ν + 1 + x ^ 2) * besselIReal (ν + 1) x
        ≤ (2 * (ν + 1) * (1 - (x / 2) ^ 2 / (ν + 2)))
          * besselIReal (ν + 1) x :=
      mul_le_mul_of_nonneg_right hcoef hI1.le
    have s2 : (2 * (ν + 1) * (1 - (x / 2) ^ 2 / (ν + 2)))
        * besselIReal (ν + 1) x
        ≤ 2 * (ν + 1) * besselRealTerm (ν + 1) 0 x := by
      have h := mul_le_mul_of_nonneg_left hup
        (by linarith : (0 : ℝ) ≤ 2 * (ν + 1))
      calc (2 * (ν + 1) * (1 - (x / 2) ^ 2 / (ν + 2)))
          * besselIReal (ν + 1) x
          = 2 * (ν + 1)
            * ((1 - (x / 2) ^ 2 / (ν + 2)) * besselIReal (ν + 1) x) := by
            ring
        _ ≤ 2 * (ν + 1) * besselRealTerm (ν + 1) 0 x := h
    have s4 : x * besselRealTerm ν 0 x < x * besselIReal ν x :=
      mul_lt_mul_of_pos_left hlo hx
    linarith [s1, s2, hid, s4]
  -- convert to ψ via multiplication by I_{ν+1}·I_ν > 0
  have hABpos : 0 < besselIReal (ν + 1) x * besselIReal ν x :=
    mul_pos hI1 hI0
  have hψmul : besselPsiReal ν x * (besselIReal (ν + 1) x * besselIReal ν x)
      = x * (besselIReal ν x * besselIReal ν x
        - besselIReal (ν + 1) x * besselIReal (ν + 1) x) := by
    unfold besselPsiReal besselRatioReal
    field_simp
  have hfin : (2 * ν + 1) * (besselIReal (ν + 1) x * besselIReal ν x)
      < x * (besselIReal ν x * besselIReal ν x
        - besselIReal (ν + 1) x * besselIReal (ν + 1) x) := by
    have h1 : besselIReal ν x
          * ((2 * ν + 1 + x ^ 2) * besselIReal (ν + 1) x)
        < besselIReal ν x * (x * besselIReal ν x) :=
      mul_lt_mul_of_pos_left hkey hI0
    have h2 : besselIReal (ν + 1) x ≤ x * besselIReal ν x := by
      have hc1 : (1 : ℝ) ≤ 2 * ν + 1 + x ^ 2 := by
        nlinarith [sq_nonneg x]
      nlinarith [hkey, hI1.le]
    have h3 : (0 : ℝ) ≤ x * besselIReal (ν + 1) x
        * (x * besselIReal ν x - besselIReal (ν + 1) x) := by
      apply mul_nonneg (mul_nonneg hx.le hI1.le)
      linarith [h2]
    nlinarith [h1, h3]
  have hlt : (2 * ν + 1) * (besselIReal (ν + 1) x * besselIReal ν x)
      < besselPsiReal ν x * (besselIReal (ν + 1) x * besselIReal ν x) := by
    rw [hψmul]
    exact hfin
  exact lt_of_mul_lt_mul_right hlt hABpos.le

end AmosClosure
