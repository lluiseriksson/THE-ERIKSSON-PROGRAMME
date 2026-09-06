import Mathlib

/-! PRE-VALIDATION: isolated generic proof step; .olean not materialized,
compiler verification pending. Run before the project draft in Colab. -/

noncomputable section

example {α β V : Type*} [Fintype α] [DecidableEq β] [AddCommMonoid V]
    (p q : α → β) (target : α) (f : α → V)
    (h : ∀ source, p target = p source ↔ q target = q source) :
    (∑ source, if p target = p source then f source else 0) =
      ∑ source, if q source = q target then f source else 0 := by
  apply Finset.sum_congr rfl
  intro source _
  apply if_congr _ rfl rfl
  exact (h source).trans eq_comm

-- Normalize the outer let before rewriting the owner-indicator sum.
example {α β V : Type*} [Fintype α] [DecidableEq β] [AddCommMonoid V]
    (p : α → β) (target : α) (f : α → V) (z : V)
    (hs : (∑ source, if p target = p source then f source else 0) = z) :
    let owner := p
    (∑ source, if owner target = owner source then f source else 0) = z := by
  dsimp only
  rw [hs]

-- A higher-order rewrite must receive the composed function explicitly.
example {α β V : Type*} [Fintype α] [AddCommMonoid V]
    (coord : α → β) (T : β → β) (F : β → V) (rhs : (β → V) → V)
    (hs : ∀ g : β → V, (∑ source, g (coord source)) = rhs g) :
    (∑ source, F (T (coord source))) = rhs (fun x => F (T x)) := by
  rw [hs (fun x => F (T x))]

end
