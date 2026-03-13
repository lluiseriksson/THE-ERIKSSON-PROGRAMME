import Mathlib
example (a b : ℝ) : a ≤ b ∨ b < a := le_or_lt a b
example (a b : ℝ) : a ≤ b ∨ b < a := le_or_gt a b
