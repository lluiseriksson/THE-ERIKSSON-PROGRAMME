/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import Mathlib
import YangMills.OS.DobrushinOscillation

/-!

> **STATUS AT THIS COMMIT: SOURCE, NOT RESULT.**  Nothing in this file has been
> elaborated.  No declaration below is `Formalized` in the sense this repository
> uses that word --- there is no compiled Lean declaration and no oracle entry
> for any of them.  A pushed source is an object available to be checked; it is
> not yet a result.  Do not cite, import, or count anything here until a focused
> elaboration, a clean oracle and a reproduced hash exist for it.
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

`popoviciu_variance_le` and the sharpness witness are the content here.  The
step from the variance bound to the covariance bound is Cauchy--Schwarz and is
NOT yet in this file; the module states what it has and does not gesture at what
it does not.
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

end Dobrushin

end YangMills.OS
