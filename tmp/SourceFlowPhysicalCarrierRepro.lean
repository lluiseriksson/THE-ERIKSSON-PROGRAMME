import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# PRE-VALIDATION: physical carrier transport, Mathlib-only repro

Source present; .olean not materialized; result not compiler-verified.
Run this before elaborating the project-dependent real-slice draft.
-/

noncomputable section

example {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (f : ι → ℂ) (x : ι) :
    ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : κ => ℂ) e f (e x) = f x := by
  change f (e.symm (e x)) = f x
  rw [Equiv.symm_apply_apply]

example {ι κ : Type*} [Fintype ι] [Fintype κ]
    (U : (ι → ℂ) ≃L[ℂ] (κ → ℂ))
    (G : (ι → ℂ) →L[ℂ] (ι → ℂ)) (f : ι → ℂ) :
    (U.toContinuousLinearMap.comp (G.comp U.symm.toContinuousLinearMap))
      (U f) = U (G f) := by
  change U (G (U.symm (U f))) = U (G f)
  rw [ContinuousLinearEquiv.symm_apply_apply]

end
