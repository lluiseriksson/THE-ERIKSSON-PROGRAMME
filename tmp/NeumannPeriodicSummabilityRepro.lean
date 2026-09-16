import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.LinearCombination

/-!
PRE-VALIDATION: Mathlib-only elaboration probe, not physical evidence.
Source present; .olean not materialized; result not compiler-verified.
-/

noncomputable section

example {d : ℕ} (x n P : Fin d → ℤ) (hP : ∀ i, P i ≠ 0) :
    Function.Injective (fun k : Fin d → ℤ => x - (fun i => n i + P i * k i)) := by
  intro k l h
  funext i
  have hi := congrFun h i
  change x i - (n i + P i * k i) = x i - (n i + P i * l i) at hi
  have hz : P i * (k i - l i) = 0 := by
    linear_combination -hi
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (hP i))

example {d : ℕ} {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (w : (Fin d → ℤ) → ℝ) (hw : Summable w)
    (index : (Fin d → ℤ) → (Fin d → ℤ)) (hi : Function.Injective index)
    (B : ℝ) (f : (Fin d → ℤ) → E)
    (hb : ∀ k, ‖f k‖ ≤ B * w (index k)) : Summable f := by
  have hs := hw.comp_injective hi
  apply Summable.of_norm_bounded (hs.mul_left B)
  exact hb

end
