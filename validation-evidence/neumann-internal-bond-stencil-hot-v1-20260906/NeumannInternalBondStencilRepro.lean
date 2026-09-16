import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# PRE-VALIDATION: adjoint-factorization Mathlib-only repro
Source present; .olean not materialized; not compiler-verified.
No physical operator or boundary conclusion is inferred from this repro.
-/

noncomputable section
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

theorem neumannBondAdjointRepro (D : E →L[ℝ] F) (R : F →L[ℝ] G)
    (X : G →L[ℝ] F) (hR : R = X.adjoint) :
    (R.comp D).adjoint = D.adjoint.comp X := by
  rw [ContinuousLinearMap.adjoint_comp, hR,
    ContinuousLinearMap.adjoint_adjoint]
end
