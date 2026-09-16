import Mathlib

/-! PRE-VALIDATION: exact residual subgoal from field-action v1 at56:2,
with the physical scalar/value abstracted. No project import or claim. -/
example {V : Type*} [Zero V] [SMul ℝ V] (w : ℝ) (v : V) :
    w • v = w • (if True then v else 0) := by
  simp only [ite_true]
