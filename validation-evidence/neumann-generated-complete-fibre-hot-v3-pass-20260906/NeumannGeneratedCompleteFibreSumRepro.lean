import Mathlib

/-!
PRE-VALIDATION: source present, .olean not materialized; not compiler verified.
Exact generic finite-sum rewriting step extracted before project elaboration.
-/

open scoped BigOperators

example (p : Prop) : p ↔ p := by
  exact Iff.rfl

example {I V : Type*} [Fintype I] [AddCommMonoid V]
    (p : I → Prop) [DecidablePred p] (f : I → V) :
    (∑ x : I, if p x then f x else 0) = ∑ x : {x : I // p x}, f x.1 := by
  classical
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := p)
    _ (fun x => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])]
