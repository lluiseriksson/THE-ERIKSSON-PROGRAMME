import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# PRE-VALIDATION: expose the beta-reduced owner weight before rewriting

Source present; no .olean is materialized and this reproduction is not
compiler-verified. It isolates the first F5 v2 error without project imports.
-/

example {ι κ β : Type*} (sourceOwner : ι → β) (targetOwner : κ → β)
    (dist : β → β → ℕ) (source : ι) (target : κ) (owner : β)
    (A rate value v : ℝ) (howner : sourceOwner source = owner)
    (hkernel : value ≤
      (fun target source => A * Real.exp
        (-(rate * (dist (targetOwner target) (sourceOwner source) : ℝ))))
        target source * v) :
    value ≤ A * Real.exp (-(rate * (dist (targetOwner target) owner : ℝ))) * v := by
  have hk : value ≤
      (A * Real.exp (-(rate *
        (dist (targetOwner target) (sourceOwner source) : ℝ)))) * v := hkernel
  rw [howner] at hk
  exact hk
