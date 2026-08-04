/- Copyright (c) 2026 Lluis Eriksson.
SPDX-License-Identifier: AGPL-3.0-or-later -/

import AmosClosure.RiccatiReal
import Mathlib.Analysis.ODE.Gronwall

/-!
# Modified-Bessel ratios on the full Gamma-series domain `ν > -1`

The original real-order interface was built for `ν ≥ 0`.  The Gamma series is
in fact positive and summable for `ν > -1`.  Instead of rebuilding the long
termwise derivative argument at negative order, this file proves the
three-term recurrence there and differentiates that recurrence using the
already verified nonnegative-order derivatives at `ν+1` and `ν+2`.
-/

open Set Filter Topology

namespace AmosClosure

lemma gamma_arg_pos_gt_neg_one (ν : ℝ) (hν : -1 < ν) (k : ℕ) :
    0 < ν + k + 1 := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

lemma besselRealTerm_pos_gt_neg_one (ν : ℝ) (hν : -1 < ν) (k : ℕ)
    {x : ℝ} (hx : 0 < x) : 0 < besselRealTerm ν k x := by
  unfold besselRealTerm
  apply div_pos
  · exact Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < x / 2) _
  · exact mul_pos (by exact_mod_cast k.factorial_pos)
      (Real.Gamma_pos_of_pos (gamma_arg_pos_gt_neg_one ν hν k))

lemma besselRealTerm_nonneg_gt_neg_one (ν : ℝ) (hν : -1 < ν) (k : ℕ)
    {x : ℝ} (hx : 0 < x) : 0 ≤ besselRealTerm ν k x :=
  (besselRealTerm_pos_gt_neg_one ν hν k hx).le

/-- The negative-order tail is an elementary rescaling of the series at
order `ν+1 ≥ 0`. -/
lemma besselRealTerm_shift_order (ν : ℝ) (hν : -1 < ν) (k : ℕ)
    {x : ℝ} (hx : 0 < x) :
    besselRealTerm ν (k + 1) x =
      (x / 2) / ((k : ℝ) + 1) * besselRealTerm (ν + 1) k x := by
  have hx2 : (0 : ℝ) < x / 2 := by linarith
  have harg : 0 < ν + k + 2 := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  unfold besselRealTerm
  have he : ν + 2 * ((k + 1 : ℕ) : ℝ) = ((ν + 1) + 2 * (k : ℝ)) + 1 := by
    push_cast
    ring
  have hp : (x / 2) ^ (ν + 2 * ((k + 1 : ℕ) : ℝ)) =
      (x / 2) ^ ((ν + 1) + 2 * (k : ℝ)) * (x / 2) := by
    rw [he, Real.rpow_add hx2, Real.rpow_one]
  have hf : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * k.factorial := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hg : Real.Gamma (ν + (k + 1 : ℕ) + 1) =
      Real.Gamma ((ν + 1) + k + 1) := by
    congr 1
    push_cast
    ring
  rw [hp, hf, hg]
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have hkf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have harg' : 0 < (ν + 1) + k + 1 := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hgamma : Real.Gamma ((ν + 1) + k + 1) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos harg')
  field_simp

theorem summable_besselRealTerm_gt_neg_one (ν : ℝ) (hν : -1 < ν)
    {x : ℝ} (hx : 0 < x) : Summable (fun k => besselRealTerm ν k x) := by
  have hν1 : 0 ≤ ν + 1 := by linarith
  have hs1 := summable_besselRealTerm (ν + 1) hν1 hx
  have htail : Summable (fun k => besselRealTerm ν (k + 1) x) := by
    have hmajor : Summable
        (fun k => (x / 2) * besselRealTerm (ν + 1) k x) :=
      hs1.mul_left (x / 2)
    refine Summable.of_nonneg_of_le
      (f := fun k => (x / 2) * besselRealTerm (ν + 1) k x)
      (fun k => besselRealTerm_nonneg_gt_neg_one ν hν (k + 1) hx) ?_ ?_
    · intro k
      rw [besselRealTerm_shift_order ν hν k hx]
      have ht := besselRealTerm_nonneg (ν + 1) hν1 k hx
      have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      have hfrac : 0 ≤ (x / 2) / ((k : ℝ) + 1) := by positivity
      have hle : (x / 2) / ((k : ℝ) + 1) ≤ x / 2 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      exact mul_le_mul_of_nonneg_right hle ht
    · exact hmajor
  exact (summable_nat_add_iff 1).mp htail

/-- Positivity of the Gamma-series Bessel function on its natural first
strip `ν > -1`. -/
theorem besselIReal_pos_gt_neg_one (ν : ℝ) (hν : -1 < ν) {x : ℝ}
    (hx : 0 < x) : 0 < besselIReal ν x := by
  have hsum := summable_besselRealTerm_gt_neg_one ν hν hx
  have h0 : besselRealTerm ν 0 x ≤ besselIReal ν x := by
    apply hsum.le_tsum 0
    intro j _
    exact besselRealTerm_nonneg_gt_neg_one ν hν j hx
  exact lt_of_lt_of_le (besselRealTerm_pos_gt_neg_one ν hν 0 hx) h0

lemma besselRealTerm_rec_zero_gt_neg_one (ν : ℝ) (hν : -1 < ν) {x : ℝ}
    (hx : 0 < x) :
    2 * (ν + 1) / x * besselRealTerm (ν + 1) 0 x =
      besselRealTerm ν 0 x := by
  have hx2 : (0 : ℝ) < x / 2 := by linarith
  unfold besselRealTerm
  simp only [Nat.cast_zero, Nat.factorial_zero, Nat.cast_one, mul_zero,
    add_zero]
  rw [Real.Gamma_add_one (ne_of_gt (by linarith : (0 : ℝ) < ν + 1)),
    Real.rpow_add hx2 ν 1, Real.rpow_one]
  have hg : Real.Gamma (ν + 1) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
  have hnu1 : ν + 1 ≠ 0 := by linarith
  have hxne : x ≠ 0 := ne_of_gt hx
  field_simp

lemma besselRealTerm_rec_succ_gt_neg_one (ν : ℝ) (hν : -1 < ν) (k : ℕ)
    {x : ℝ} (hx : 0 < x) :
    2 * (ν + 1) / x * besselRealTerm (ν + 1) (k + 1) x =
      besselRealTerm ν (k + 1) x - besselRealTerm (ν + 2) k x := by
  have hx2 : (0 : ℝ) < x / 2 := by linarith
  have harg2 : (0 : ℝ) < ν + k + 2 := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  unfold besselRealTerm
  have heL : (ν + 1) + 2 * ((k + 1 : ℕ) : ℝ) =
      (ν + 2 * ((k + 1 : ℕ) : ℝ)) + 1 := by
    push_cast
    ring
  have heR : (ν + 2) + 2 * ((k : ℕ) : ℝ) =
      ν + 2 * ((k + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  have hsplitL : (x / 2) ^ ((ν + 1) + 2 * ((k + 1 : ℕ) : ℝ)) =
      (x / 2) ^ (ν + 2 * ((k + 1 : ℕ) : ℝ)) * (x / 2) := by
    rw [heL, Real.rpow_add hx2, Real.rpow_one]
  have hgL : Real.Gamma ((ν + 1) + (k + 1 : ℕ) + 1) =
      (ν + k + 2) * Real.Gamma (ν + k + 2) := by
    rw [show (ν + 1) + ((k + 1 : ℕ) : ℝ) + 1 = (ν + k + 2) + 1 by
      push_cast
      ring]
    exact Real.Gamma_add_one (ne_of_gt harg2)
  have hgR2 : Real.Gamma ((ν + 2) + (k : ℕ) + 1) =
      (ν + k + 2) * Real.Gamma (ν + k + 2) := by
    rw [show (ν + 2) + ((k : ℕ) : ℝ) + 1 = (ν + k + 2) + 1 by ring]
    exact Real.Gamma_add_one (ne_of_gt harg2)
  have hgR1 : Real.Gamma (ν + (k + 1 : ℕ) + 1) =
      Real.Gamma (ν + k + 2) := by
    rw [show ν + ((k + 1 : ℕ) : ℝ) + 1 = ν + k + 2 by
      push_cast
      ring]
  have hfact : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * k.factorial := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hsplitL, heR, hgL, hgR2, hgR1, hfact]
  have hf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hg : Real.Gamma (ν + k + 2) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos harg2)
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have ha2 : ν + k + 2 ≠ 0 := ne_of_gt harg2
  field_simp
  ring

/-- The three-term recurrence extends from `ν ≥ 0` to the full positive
Gamma-series strip `ν > -1`. -/
theorem besselIReal_recurrence_gt_neg_one (ν : ℝ) (hν : -1 < ν) {x : ℝ}
    (hx : 0 < x) :
    besselIReal ν x - besselIReal (ν + 2) x =
      2 * (ν + 1) / x * besselIReal (ν + 1) x := by
  have hs0 := summable_besselRealTerm_gt_neg_one ν hν hx
  have hs1 := summable_besselRealTerm (ν + 1) (by linarith) hx
  have hs2 := summable_besselRealTerm (ν + 2) (by linarith) hx
  have hs1' : Summable
      (fun k => 2 * (ν + 1) / x * besselRealTerm (ν + 1) k x) :=
    hs1.mul_left _
  have hsn_shift : Summable (fun k => besselRealTerm ν (k + 1) x) :=
    (summable_nat_add_iff 1).mpr hs0
  have hrhs : 2 * (ν + 1) / x * besselIReal (ν + 1) x =
      besselRealTerm ν 0 x +
        ∑' k, (besselRealTerm ν (k + 1) x - besselRealTerm (ν + 2) k x) := by
    rw [besselIReal, ← tsum_mul_left, hs1'.tsum_eq_zero_add]
    rw [besselRealTerm_rec_zero_gt_neg_one ν hν hx]
    congr 1
    exact tsum_congr fun k => besselRealTerm_rec_succ_gt_neg_one ν hν k hx
  have hsplit :
      ∑' k, (besselRealTerm ν (k + 1) x - besselRealTerm (ν + 2) k x) =
        (∑' k, besselRealTerm ν (k + 1) x) -
          ∑' k, besselRealTerm (ν + 2) k x :=
    Summable.tsum_sub hsn_shift hs2
  have hleft : besselIReal ν x =
      besselRealTerm ν 0 x + ∑' k, besselRealTerm ν (k + 1) x := by
    rw [besselIReal, hs0.tsum_eq_zero_add]
  rw [hrhs, hsplit, hleft, besselIReal]
  ring

/-- The derivative identity on `ν > -1`.  For negative `ν`, it is obtained
by differentiating the recurrence into the already formalized nonnegative
orders. -/
theorem besselIReal_hasDerivAt_gt_neg_one (ν : ℝ) (hν : -1 < ν) {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt (fun y => besselIReal ν y)
      (besselIReal (ν + 1) x + ν / x * besselIReal ν x) x := by
  by_cases hν0 : 0 ≤ ν
  · exact besselIReal_hasDerivAt ν hν0 hx
  have hνneg : ν < 0 := lt_of_not_ge hν0
  have h1 := besselIReal_hasDerivAt (ν + 1) (by linarith) hx
  have h2 := besselIReal_hasDerivAt (ν + 2) (by linarith) hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hc : HasDerivAt (fun y : ℝ => 2 * (ν + 1) / y)
      (-(2 * (ν + 1)) / x ^ 2) x := by
    convert (hasDerivAt_const x (2 * (ν + 1))).div (hasDerivAt_id x) hx0 using 1 <;>
      simp only [id_eq] <;> field_simp <;> ring
  have hright := h2.add (hc.mul h1)
  have heq : (fun y => besselIReal ν y) =ᶠ[𝓝 x]
      (fun y => besselIReal (ν + 2) y +
        (2 * (ν + 1) / y) * besselIReal (ν + 1) y) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    have hr := besselIReal_recurrence_gt_neg_one ν hν hy
    linarith
  have hder := HasDerivAt.congr_of_eventuallyEq hright heq
  have hr0 := besselIReal_recurrence_gt_neg_one ν hν hx
  have hr1 := besselIReal_recurrence (ν + 1) (by linarith) hx
  convert hder using 1
  field_simp [hx0] at hr0 hr1 ⊢
  ring_nf at hr0 hr1 ⊢
  linear_combination ν * hr0 + x * hr1

lemma besselRatioReal_pos_gt_neg_one {ν : ℝ} (hν : -1 < ν) {x : ℝ}
    (hx : 0 < x) : 0 < besselRatioReal ν x :=
  div_pos (besselIReal_pos_gt_neg_one (ν + 1) (by linarith) hx)
    (besselIReal_pos_gt_neg_one ν hν hx)

theorem besselRatioReal_hasDerivAt_gt_neg_one (ν : ℝ) (hν : -1 < ν)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (besselRatioReal ν)
      (riccatiQReal ν x (besselRatioReal ν x)) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hI0 := besselIReal_pos_gt_neg_one ν hν hx
  have hf := besselIReal_hasDerivAt_gt_neg_one (ν + 1) (by linarith) hx
  have hg := besselIReal_hasDerivAt_gt_neg_one ν hν hx
  rw [show ν + 1 + 1 = ν + 2 by ring] at hf
  have hdiv := hf.div hg (ne_of_gt hI0)
  have hrec := besselIReal_recurrence_gt_neg_one ν hν hx
  have hI2 : besselIReal (ν + 2) x =
      besselIReal ν x - 2 * (ν + 1) / x * besselIReal (ν + 1) x := by
    linarith
  rw [hI2] at hdiv
  convert hdiv using 1
  unfold riccatiQReal besselRatioReal
  field_simp [hx0]
  ring

end AmosClosure
