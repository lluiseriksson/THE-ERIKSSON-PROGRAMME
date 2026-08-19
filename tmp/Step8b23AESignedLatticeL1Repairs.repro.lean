import Mathlib

open scoped BigOperators

noncomputable section

private def step8b23TestL1Length {d : ℕ} (u : Fin d → ℤ) : ℝ :=
  ∑ mu, (Int.natAbs (u mu) : ℝ)

example : Summable (fun _u : Fin 0 → ℤ => (1 : ℝ)) := by
  exact Summable.of_finite

example {d : ℕ} (u : Fin d → ℤ) :
    step8b23TestL1Length (fun mu ↦ -u mu) = step8b23TestL1Length u := by
  unfold step8b23TestL1Length
  simp

example {M : ℕ} {x : ℝ} (hcenter : x ≤ 2 * (M : ℝ)) :
    x ≤ ((4 : ℕ) : ℝ) * (M : ℝ) / 2 := by
  nlinarith [hcenter]
