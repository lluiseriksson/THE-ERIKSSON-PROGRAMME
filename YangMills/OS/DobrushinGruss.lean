/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import Mathlib
import YangMills.OS.DobrushinOscillation

/-!
# The quarter constant: Popoviciu's variance bound, and where it is attained

Charter: `docs/DOBRUSHIN-D3-CHARTER.md`.  Gate `judge_dobrushin_d3b.py` (J10q),
committed before this file.

## Why this is its own module, and NOT a dependency of D-3c

The local oscillation transport of D-3c needs only D-3a.  Keeping the quarter
constant here means that a library difficulty in the Cauchy--Schwarz step cannot
block the central rung.  Nothing in `DobrushinRowSum.lean` or in the
oscillation-transport lemma imports this file.

## What forced the constant

The first covariance gate reported worst ratios `0.2403` and `0.2217` against a
bound with constant one --- within a percent of `1/4`, which is not slack but a
signal.  A single fair Bernoulli site with `f = g` the indicator of one state has
`Cov = 1/4` and `osc f = osc g = 1`, so **no inequality of this shape can hold
with a constant below `1/4`**, and mechanising the constant-one version would
have formalised a statement four times weaker than the available one.

`popoviciu_variance_le` is the algebraic half and needs no spectral theory:
from `(f x - m) * (M - f x) ≥ 0` one gets `f x ^ 2 ≤ (m + M) * f x - m * M`,
and averaging gives `Var f ≤ (M - E f) * (E f - m) ≤ (M - m)^2 / 4`.

## Status

`popoviciu_variance_le` and its sharpness witness are the algebraic half.  The
covariance bound `gruss_covariance_le` is now here too, together with its own
attainment witness `gruss_attained` — the three endpoints Amendment 1 of the
charter names, kept separate.  The covariance route is deliberately NOT
Cauchy--Schwarz: the centred mass `x ↦ p x * (f x - E f)` has total zero, so
`abs_sum_signed_le` of D-3a controls it against `osc g` at the price of half a
mean absolute deviation, and `mad_le_half_spread` supplies the second half.
Each factor `1/2` is born in exactly one lemma; `1/4` is their product, the
same way the charter's reserve route promised it, and Popoviciu is consumed by
none of it — a library difficulty in either half cannot touch the other.
-/

namespace YangMills.OS

namespace Dobrushin

open Finset

variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]

/-! ## §1  Expectation and variance for a finite weight -/

/-- The expectation of `f` under a finite weight `p`. -/
noncomputable def expect (p f : S → ℝ) : ℝ := ∑ x, p x * f x

/-- The variance of `f` under a finite weight `p`. -/
noncomputable def variance (p f : S → ℝ) : ℝ :=
  expect p (fun x => f x * f x) - expect p f * expect p f

/-! ## §2  Popoviciu, by the pointwise quadratic -/

/-- The pointwise inequality that carries everything: if `m ≤ f x ≤ M` then
`f x ^ 2 ≤ (m + M) * f x - m * M`, which is just `(f x - m) * (M - f x) ≥ 0`
rearranged. -/
theorem sq_le_of_mem_Icc {m M t : ℝ} (h1 : m ≤ t) (h2 : t ≤ M) :
    t * t ≤ (m + M) * t - m * M := by
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

/-- **Popoviciu's variance bound.**  For a probability weight `p` and `f` with
range in `[m, M]`, the variance is at most `(M - m)^2 / 4`. -/
theorem popoviciu_variance_le {p f : S → ℝ} {m M : ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hm : ∀ x, m ≤ f x) (hM : ∀ x, f x ≤ M) :
    variance p f ≤ (M - m) ^ 2 / 4 := by
  have hEsq : expect p (fun x => f x * f x)
      ≤ (m + M) * expect p f - m * M := by
    unfold expect
    have hterm : ∀ x ∈ (Finset.univ : Finset S),
        p x * (f x * f x) ≤ p x * ((m + M) * f x - m * M) := fun x _ =>
      mul_le_mul_of_nonneg_left (sq_le_of_mem_Icc (hm x) (hM x)) (hp0 x)
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    have : ∑ x, p x * ((m + M) * f x - m * M)
        = (m + M) * (∑ x, p x * f x) - (m * M) * (∑ x, p x) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [this, hp1, mul_one]
  have hkey : variance p f ≤ (M - expect p f) * (expect p f - m) := by
    unfold variance
    nlinarith [hEsq]
  refine hkey.trans ?_
  nlinarith [sq_nonneg (M + m - 2 * expect p f)]

/-! ## §3  Sharpness: the constant cannot be lowered -/

/-- The fair two-point weight. -/
noncomputable def fairTwo : Fin 2 → ℝ := fun _ => (1 : ℝ) / 2

/-- The indicator of the second point. -/
noncomputable def indOne : Fin 2 → ℝ := fun x => if x = 1 then (1 : ℝ) else 0

theorem fairTwo_nonneg (x : Fin 2) : 0 ≤ fairTwo x := by
  unfold fairTwo; norm_num

theorem fairTwo_sum : ∑ x : Fin 2, fairTwo x = 1 := by
  rw [Fin.sum_univ_two]; unfold fairTwo; norm_num

theorem indOne_lower (x : Fin 2) : (0 : ℝ) ≤ indOne x := by
  unfold indOne; split <;> norm_num

theorem indOne_upper (x : Fin 2) : indOne x ≤ 1 := by
  unfold indOne; split <;> norm_num

/-- **Sharpness.**  On the fair two-point weight with `f` the indicator of one
point, the variance is exactly `1/4`, which is `(M - m)^2 / 4` for `m = 0`,
`M = 1`.  Hence the constant `1/4` of `popoviciu_variance_le` cannot be
lowered, and neither can the constant of any covariance bound derived from
it. -/
theorem popoviciu_attained : variance fairTwo indOne = (1 - 0) ^ 2 / 4 := by
  unfold variance expect fairTwo indOne
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  norm_num

/-! ## §4  Bounds on the expectation -/

theorem le_expect {p f : S → ℝ} {m : ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (hm : ∀ x, m ≤ f x) :
    m ≤ expect p f := by
  unfold expect
  have h : ∑ x, p x * m ≤ ∑ x, p x * f x :=
    Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hm x) (hp0 x)
  rw [← Finset.sum_mul, hp1, one_mul] at h
  exact h

theorem expect_le {p f : S → ℝ} {M : ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (hM : ∀ x, f x ≤ M) :
    expect p f ≤ M := by
  unfold expect
  have h : ∑ x, p x * f x ≤ ∑ x, p x * M :=
    Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hM x) (hp0 x)
  rw [← Finset.sum_mul, hp1, one_mul] at h
  exact h

/-- Any uniform bounds enclose the oscillation. -/
theorem osc_le_of_bounds {g : S → ℝ} {m M : ℝ}
    (hm : ∀ x, m ≤ g x) (hM : ∀ x, g x ≤ M) : osc g ≤ M - m := by
  unfold osc
  have h1 : Finset.univ.sup' Finset.univ_nonempty g ≤ M :=
    Finset.sup'_le _ _ fun x _ => hM x
  have h2 : m ≤ Finset.univ.inf' Finset.univ_nonempty g :=
    Finset.le_inf' _ _ fun x _ => hm x
  linarith

/-! ## §5  The mean absolute deviation about the mean -/

/-- The mean absolute deviation of `f` about its `p`-mean. -/
noncomputable def mad (p f : S → ℝ) : ℝ := ∑ x, p x * |f x - expect p f|

theorem mad_nonneg {p : S → ℝ} (hp0 : ∀ x, 0 ≤ p x) (f : S → ℝ) :
    0 ≤ mad p f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hp0 x) (abs_nonneg _)

/-- **The mean absolute deviation about the mean is at most half the spread** —
the `L¹` companion of Popoviciu's `L²` bound, and the lemma in which one of the
two halves of the quarter constant is born.  Attained by the fair two-point
weight on the endpoints of `[m, M]`. -/
theorem mad_le_half_spread {p f : S → ℝ} {m M : ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hm : ∀ x, m ≤ f x) (hM : ∀ x, f x ≤ M) :
    mad p f ≤ (M - m) / 2 := by
  set A := expect p f with hAdef
  have hmA : m ≤ A := le_expect hp0 hp1 hm
  have hAM : A ≤ M := expect_le hp0 hp1 hM
  -- positive and negative parts of the deviation
  have habs : ∀ x : S, |f x - A| = max (f x - A) 0 + max (A - f x) 0 := by
    intro x
    rcases le_total (f x) A with h | h
    · rw [abs_of_nonpos (by linarith), max_eq_right (by linarith),
        max_eq_left (by linarith)]
      ring
    · rw [abs_of_nonneg (by linarith), max_eq_left (by linarith),
        max_eq_right (by linarith)]
      ring
  have hsplit : mad p f
      = (∑ x, p x * max (f x - A) 0) + ∑ x, p x * max (A - f x) 0 := by
    unfold mad
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← hAdef, habs x]
    ring
  -- the two parts are equal, because the mass is centred
  have hPeqN : (∑ x, p x * max (f x - A) 0) = ∑ x, p x * max (A - f x) 0 := by
    have hpt : ∀ x : S,
        p x * max (f x - A) 0 - p x * max (A - f x) 0 = p x * (f x - A) := by
      intro x
      rcases le_total (f x) A with h | h
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
        ring
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
        ring
    have hzero : (∑ x, p x * max (f x - A) 0) - ∑ x, p x * max (A - f x) 0 = 0 := by
      rw [← Finset.sum_sub_distrib]
      have h1 : ∑ x, (p x * max (f x - A) 0 - p x * max (A - f x) 0)
          = ∑ x, p x * (f x - A) := Finset.sum_congr rfl fun x _ => hpt x
      rw [h1]
      have h2 : ∑ x, p x * (f x - A) = (∑ x, p x * f x) - A * ∑ x, p x := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun x _ => by ring
      rw [h2, hp1, mul_one, hAdef]
      unfold expect
      ring
    linarith
  -- indicator-weighted bounds on each part
  have hT0 : (0 : ℝ) ≤ ∑ x, p x * (if A ≤ f x then (1 : ℝ) else 0) :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hp0 x) (by split <;> norm_num)
  have hT1 : (∑ x, p x * (if A ≤ f x then (1 : ℝ) else 0)) ≤ 1 := by
    rw [← hp1]
    refine Finset.sum_le_sum fun x _ => ?_
    rcases le_or_lt A (f x) with h | h
    · rw [if_pos h, mul_one]
    · rw [if_neg (not_le.mpr h), mul_zero]
      exact hp0 x
  set T := ∑ x, p x * (if A ≤ f x then (1 : ℝ) else 0) with hTdef
  have hposT : (∑ x, p x * max (f x - A) 0) ≤ (M - A) * T := by
    rw [hTdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rcases le_or_lt A (f x) with h | h
    · rw [if_pos h, mul_one, max_eq_left (by linarith)]
      calc p x * (f x - A) ≤ p x * (M - A) :=
            mul_le_mul_of_nonneg_left (by linarith [hM x]) (hp0 x)
        _ = (M - A) * p x := mul_comm _ _
    · rw [if_neg (not_le.mpr h), mul_zero, mul_zero,
        max_eq_right (by linarith)]
      norm_num
  have hnegT : (∑ x, p x * max (A - f x) 0) ≤ (A - m) * (1 - T) := by
    have h1T : (A - m) * (1 - T)
        = ∑ x, p x * ((A - m) * (1 - if A ≤ f x then (1 : ℝ) else 0)) := by
      rw [hTdef]
      have hexp : ∑ x, p x * ((A - m) * (1 - if A ≤ f x then (1 : ℝ) else 0))
          = (A - m) * ((∑ x, p x)
              - ∑ x, p x * (if A ≤ f x then (1 : ℝ) else 0)) := by
        rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun x _ => by ring
      rw [hexp, hp1]
    rw [h1T]
    refine Finset.sum_le_sum fun x _ => ?_
    rcases le_or_lt A (f x) with h | h
    · rw [if_pos h, max_eq_right (by linarith)]
      simp only [mul_zero, sub_self]
      exact le_refl 0
    · rw [if_neg (not_le.mpr h), max_eq_left (by linarith)]
      have : (A - m) * (1 - 0) = A - m := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left (by linarith [hm x]) (hp0 x)
  -- the square comparison
  have hMA : (0 : ℝ) ≤ M - A := by linarith
  have hAm : (0 : ℝ) ≤ A - m := by linarith
  have hpos0 : (0 : ℝ) ≤ ∑ x, p x * max (f x - A) 0 :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hp0 x) (le_max_right _ _)
  set P := ∑ x, p x * max (f x - A) 0 with hPdef
  have hprod : P * P ≤ ((M - A) * T) * ((A - m) * (1 - T)) := by
    have hP2 : P ≤ (A - m) * (1 - T) := by rw [hPeqN]; exact hnegT
    exact mul_le_mul hposT hP2 hpos0 (mul_nonneg hMA hT0)
  have hsq : P * P ≤ ((M - m) / 4) * ((M - m) / 4) := by
    nlinarith [hprod, mul_nonneg (mul_nonneg hMA hAm) (sq_nonneg (2 * T - 1)),
      sq_nonneg (M + m - 2 * A), hT0, hT1, hMA, hAm]
  have hq0 : (0 : ℝ) ≤ (M - m) / 4 := by linarith
  have hPle : P ≤ (M - m) / 4 := by
    by_contra hlt
    push_neg at hlt
    have hgt : ((M - m) / 4) * ((M - m) / 4) < P * P := by nlinarith [hq0, hlt]
    linarith [hsq]
  rw [hsplit, ← hPeqN]
  linarith

/-! ## §6  The covariance bound — the quarter constant, by the signed-mass
route

NOT Cauchy--Schwarz: the centred mass `x ↦ p x * (f x - E f)` has total zero,
so `abs_sum_signed_le` of D-3a tests it against `g` at the price of
`(∑|·|)/2 · osc g`, and `∑|·|` is exactly the mean absolute deviation, at most
`(M₁ - m₁)/2` by §5.  The two halves multiply into the quarter. -/

/-- **`gruss_covariance_le`** — the covariance of `f` and `g` under a
probability weight is at most a quarter of the product of the spreads. -/
theorem gruss_covariance_le {p f g : S → ℝ} {m₁ M₁ m₂ M₂ : ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hm₁ : ∀ x, m₁ ≤ f x) (hM₁ : ∀ x, f x ≤ M₁)
    (hm₂ : ∀ x, m₂ ≤ g x) (hM₂ : ∀ x, g x ≤ M₂) :
    |expect p (fun x => f x * g x) - expect p f * expect p g|
      ≤ (M₁ - m₁) * (M₂ - m₂) / 4 := by
  have hzero : ∑ x, p x * (f x - expect p f) = 0 := by
    have h : ∑ x, p x * (f x - expect p f)
        = (∑ x, p x * f x) - expect p f * ∑ x, p x := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [h, hp1, mul_one]
    unfold expect
    ring
  have hrepr : expect p (fun x => f x * g x) - expect p f * expect p g
      = ∑ x, (p x * (f x - expect p f)) * g x := by
    have h : ∑ x, (p x * (f x - expect p f)) * g x
        = (∑ x, p x * (f x * g x)) - expect p f * ∑ x, p x * g x := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [h]
    unfold expect
  have hkey := abs_sum_signed_le hzero g
  have habs_a : ∑ x, |p x * (f x - expect p f)| = mad p f := by
    unfold mad
    exact Finset.sum_congr rfl fun x _ => by
      rw [abs_mul, abs_of_nonneg (hp0 x)]
  have hoscg : osc g ≤ M₂ - m₂ := osc_le_of_bounds hm₂ hM₂
  have hmadf : mad p f ≤ (M₁ - m₁) / 2 := mad_le_half_spread hp0 hp1 hm₁ hM₁
  rw [hrepr]
  refine hkey.trans ?_
  rw [habs_a]
  have hstep1 : mad p f / 2 * osc g ≤ (M₁ - m₁) / 4 * osc g :=
    mul_le_mul_of_nonneg_right (by linarith) (osc_nonneg g)
  have hM₁m₁ : (0 : ℝ) ≤ M₁ - m₁ := by
    obtain ⟨x⟩ := ‹Nonempty S›
    linarith [hm₁ x, hM₁ x]
  have hstep2 : (M₁ - m₁) / 4 * osc g ≤ (M₁ - m₁) / 4 * (M₂ - m₂) :=
    mul_le_mul_of_nonneg_left hoscg (by linarith)
  calc mad p f / 2 * osc g
      ≤ (M₁ - m₁) / 4 * osc g := hstep1
    _ ≤ (M₁ - m₁) / 4 * (M₂ - m₂) := hstep2
    _ = (M₁ - m₁) * (M₂ - m₂) / 4 := by ring

/-- The oscillation form: covariance is at most a quarter of the product of the
oscillations. -/
theorem gruss_covariance_osc_le {p f g : S → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) :
    |expect p (fun x => f x * g x) - expect p f * expect p g|
      ≤ osc f * osc g / 4 := by
  have h := gruss_covariance_le
    (m₁ := Finset.univ.inf' Finset.univ_nonempty f)
    (M₁ := Finset.univ.sup' Finset.univ_nonempty f)
    (m₂ := Finset.univ.inf' Finset.univ_nonempty g)
    (M₂ := Finset.univ.sup' Finset.univ_nonempty g)
    hp0 hp1 (inf_le_apply f) (apply_le_sup f) (inf_le_apply g) (apply_le_sup g)
  calc |expect p (fun x => f x * g x) - expect p f * expect p g|
      ≤ (Finset.univ.sup' Finset.univ_nonempty f
          - Finset.univ.inf' Finset.univ_nonempty f)
        * (Finset.univ.sup' Finset.univ_nonempty g
          - Finset.univ.inf' Finset.univ_nonempty g) / 4 := h
    _ = osc f * osc g / 4 := by unfold osc

/-- **`gruss_attained`** — on the fair two-point weight with `f = g` the
indicator of one point, the covariance is exactly `1/4`, which is the bound of
`gruss_covariance_le` at `m = 0`, `M = 1`.  The quarter cannot be lowered. -/
theorem gruss_attained :
    |expect fairTwo (fun x => indOne x * indOne x)
        - expect fairTwo indOne * expect fairTwo indOne|
      = (1 - 0) * (1 - 0) / 4 := by
  unfold expect fairTwo indOne
  norm_num [Fin.sum_univ_two]

end Dobrushin

end YangMills.OS
