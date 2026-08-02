/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import Mathlib

/-!

> **STATUS AT THIS COMMIT: SOURCE, NOT RESULT.**  Nothing in this file has been
> elaborated.  No declaration below is `Formalized` in the sense this repository
> uses that word --- there is no compiled Lean declaration and no oracle entry
> for any of them.  A pushed source is an object available to be checked; it is
> not yet a result.  Do not cite, import, or count anything here until a focused
> elaboration, a clean oracle and a reproduced hash exist for it.
# D-3a — oscillation, and what a zero-sum signed mass can do against it

Charter: `docs/DOBRUSHIN-D3-CHARTER.md`.  Gates
`scripts/judge_dobrushin_d3.py` (J8) and `scripts/judge_dobrushin_d3b.py`,
both committed before this file.

## CONVENTIONS, frozen here so that no factor can move silently later

```
    osc g          =  (sup over the finite type of g)  -  (inf over it)
    TV p q         =  (1/2) * sum_x |p x - q x|
    deltaAt i f    =  sup over eta, eta' agreeing OFF i, of |f eta - f eta'|
```
The factor `1/2` in `TV` and the factor `1` in the conclusion of
`abs_sum_signed_le` are tied to each other by exactly these definitions.  A
later change to either without the other silently changes every downstream
constant, so both are stated here and neither is defined anywhere else.

## What this module is for

The whole of D-3 rests on one elementary estimate: a signed mass of **total
zero** cannot see a constant, so it can only exploit the *spread* of the
function it is tested against.  Written for a zero-sum signed mass rather than
for a difference of two probabilities, because that is the reusable form and
because it keeps the `1/2` visible:

```
    sum_x a x = 0   ->   |sum_x a x * g x|  <=  (1/2) * (sum_x |a x|) * osc g
```

The specialisation `a = p - q` is the total-variation form used by D-3c.

## The five endpoints, kept separate on purpose

1. `sum_zero_sub_const`     — a zero-sum mass kills constants;
2. `abs_sub_mid_le`         — every value is within half an oscillation of the
                              midpoint of the range;
3. `abs_sum_signed_le`      — the signed inequality;
4. `abs_sum_sub_le_tv_mul_osc` — the TV/oscillation corollary;
5. `signed_bound_attained`  — a witness that the bound is reached, so the
                              constant is the constant and not a number above it.

They are separate so that the normalisation of `TV` and the factor `1/2` cannot
end up hidden inside the proof of D-3c.
-/

namespace YangMills.OS

namespace Dobrushin

open Finset

variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]

/-! ## §1  Oscillation and midpoint -/

/-- The oscillation of a real function on a finite nonempty type. -/
noncomputable def osc (g : S → ℝ) : ℝ :=
  (Finset.univ.sup' Finset.univ_nonempty g) -
    (Finset.univ.inf' Finset.univ_nonempty g)

/-- The midpoint of the range. -/
noncomputable def mid (g : S → ℝ) : ℝ :=
  ((Finset.univ.sup' Finset.univ_nonempty g) +
    (Finset.univ.inf' Finset.univ_nonempty g)) / 2

theorem inf_le_apply (g : S → ℝ) (x : S) :
    Finset.univ.inf' Finset.univ_nonempty g ≤ g x :=
  Finset.inf'_le g (Finset.mem_univ x)

theorem apply_le_sup (g : S → ℝ) (x : S) :
    g x ≤ Finset.univ.sup' Finset.univ_nonempty g :=
  Finset.le_sup' g (Finset.mem_univ x)

theorem osc_nonneg (g : S → ℝ) : 0 ≤ osc g := by
  obtain ⟨x⟩ := ‹Nonempty S›
  have h1 := inf_le_apply g x
  have h2 := apply_le_sup g x
  unfold osc
  linarith

/-- **Endpoint 2.**  Every value lies within half an oscillation of the midpoint
of the range.  This is the only place the factor `1/2` is created. -/
theorem abs_sub_mid_le (g : S → ℝ) (x : S) : |g x - mid g| ≤ osc g / 2 := by
  have h1 := inf_le_apply g x
  have h2 := apply_le_sup g x
  unfold mid osc
  rw [abs_le]
  constructor <;> linarith

/-! ## §2  A zero-sum signed mass -/

/-- **Endpoint 1.**  A signed mass of total zero cannot see a constant. -/
theorem sum_zero_sub_const {a : S → ℝ} (ha : ∑ x, a x = 0) (g : S → ℝ) (c : ℝ) :
    ∑ x, a x * (g x - c) = ∑ x, a x * g x := by
  have : ∑ x, a x * (g x - c) = (∑ x, a x * g x) - (∑ x, a x) * c := by
    rw [Finset.sum_mul]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [this, ha, zero_mul, sub_zero]

/-- **Endpoint 3, the signed inequality.**  A zero-sum signed mass tested against
`g` is controlled by half its total variation times the oscillation of `g`. -/
theorem abs_sum_signed_le {a : S → ℝ} (ha : ∑ x, a x = 0) (g : S → ℝ) :
    |∑ x, a x * g x| ≤ (∑ x, |a x|) / 2 * osc g := by
  rw [← sum_zero_sub_const ha g (mid g)]
  calc |∑ x, a x * (g x - mid g)|
      ≤ ∑ x, |a x * (g x - mid g)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, |a x| * |g x - mid g| :=
        Finset.sum_congr rfl fun x _ => abs_mul _ _
    _ ≤ ∑ x, |a x| * (osc g / 2) :=
        Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (abs_sub_mid_le g x) (abs_nonneg _)
    _ = (∑ x, |a x|) / 2 * osc g := by
        rw [← Finset.sum_mul]; ring

/-! ## §3  The total-variation form -/

/-- Total variation distance, with the `1/2` in the definition. -/
noncomputable def TV (p q : S → ℝ) : ℝ := (∑ x, |p x - q x|) / 2

theorem TV_nonneg (p q : S → ℝ) : 0 ≤ TV p q := by
  unfold TV
  have : 0 ≤ ∑ x, |p x - q x| :=
    Finset.sum_nonneg fun x _ => abs_nonneg _
  linarith

/-- **Endpoint 4.**  The corollary D-3c consumes: two distributions of equal
total mass differ, against any `g`, by at most `TV` times the oscillation. -/
theorem abs_sum_sub_le_tv_mul_osc {p q : S → ℝ}
    (h : ∑ x, p x = ∑ x, q x) (g : S → ℝ) :
    |∑ x, (p x - q x) * g x| ≤ TV p q * osc g := by
  have hzero : ∑ x, (p x - q x) = 0 := by
    rw [Finset.sum_sub_distrib, h, sub_self]
  have := abs_sum_signed_le hzero g
  unfold TV
  exact this

/-! ## §4  The bound is attained

Without this the constant would be a number above the truth rather than the
truth.  Two point masses sitting on a maximum and a minimum of `g` reach it. -/

/-- **Endpoint 5.**  On a two-point type, `p` concentrated at one point and `q`
at the other, tested against the indicator of the first, the inequality of
`abs_sum_sub_le_tv_mul_osc` is an EQUALITY. -/
theorem signed_bound_attained :
    |∑ x : Fin 2, ((if x = 0 then (1:ℝ) else 0) - (if x = 1 then (1:ℝ) else 0)) *
        (if x = 0 then (1:ℝ) else 0)|
      = TV (fun x : Fin 2 => if x = 0 then (1:ℝ) else 0)
            (fun x : Fin 2 => if x = 1 then (1:ℝ) else 0) *
        osc (fun x : Fin 2 => if x = 0 then (1:ℝ) else 0) := by
  have hL : |∑ x : Fin 2, ((if x = 0 then (1:ℝ) else 0) -
      (if x = 1 then (1:ℝ) else 0)) * (if x = 0 then (1:ℝ) else 0)| = 1 := by
    rw [Fin.sum_univ_two]
    norm_num
  have hT : TV (fun x : Fin 2 => if x = 0 then (1:ℝ) else 0)
      (fun x : Fin 2 => if x = 1 then (1:ℝ) else 0) = 1 := by
    unfold TV
    rw [Fin.sum_univ_two]
    norm_num
  have hO : osc (fun x : Fin 2 => if x = 0 then (1:ℝ) else 0) = 1 := by
    unfold osc
    have hs : Finset.univ.sup' Finset.univ_nonempty
        (fun x : Fin 2 => if x = 0 then (1:ℝ) else 0) = 1 := by
      refine le_antisymm (Finset.sup'_le _ _ fun x _ => ?_) ?_
      · by_cases h : x = 0 <;> simp [h]
      · exact Finset.le_sup' _ (Finset.mem_univ (0 : Fin 2)) |>.trans_eq (by norm_num)
    have hi : Finset.univ.inf' Finset.univ_nonempty
        (fun x : Fin 2 => if x = 0 then (1:ℝ) else 0) = 0 := by
      refine le_antisymm ?_ (Finset.le_inf' _ _ fun x _ => ?_)
      · exact (Finset.inf'_le _ (Finset.mem_univ (1 : Fin 2))).trans_eq (by norm_num)
      · by_cases h : x = 0 <;> simp [h]
    rw [hs, hi]; norm_num
  rw [hL, hT, hO]; norm_num

end Dobrushin

end YangMills.OS
