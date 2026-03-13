import Mathlib
open Real

-- Fix div_le_div
example (a b c : ℝ) (hc : 0 < c) (h : a ≤ b) : a / c ≤ b / c := by
  exact?

-- Fix indicator_nonneg  
example {α : Type*} (s : Set α) (U : α) : 0 ≤ s.indicator (fun _ => (1 : ℝ)) U :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) U

-- Fix exp ≤ 1
example (x : ℝ) (hx : x ≤ 0) : exp x ≤ 1 :=
  Real.exp_le_one_iff.mpr hx
