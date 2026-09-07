import Mathlib.Logic.Function.Basic

theorem neumannFixedSourceProjectionRepro {α β γ : Type}
    (n : γ) : Function.Injective (fun p : α × β => (p.1, p.2, n)) := by
  intro p q he
  exact Prod.ext (congrArg (fun a : α × β × γ => a.1) he)
    (congrArg (fun a : α × β × γ => a.2.1) he)

#print axioms neumannFixedSourceProjectionRepro
