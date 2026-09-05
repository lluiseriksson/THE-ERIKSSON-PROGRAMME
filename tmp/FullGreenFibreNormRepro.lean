import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# PRE-VALIDATION: Mathlib-only reproduction for the F5 fibre norm step

Source is present; `.olean` has not been materialized and these examples
are not compiler-verified. Run in Colab before the project-dependent drafts.
-/

noncomputable section

example {ι : Type*} [Fintype ι] (c : ℂ)
    (v w : EuclideanSpace ℂ ι) (h : ∀ i, w i = c * v i) :
    ‖w‖ = ‖c‖ * ‖v‖ := by
  have heq : w = c • v := by
    apply PiLp.ext
    intro i
    exact h i
  rw [heq, norm_smul]

example {ι : Type*} [Fintype ι] (v : EuclideanSpace ℝ ι) :
    ‖(WithLp.toLp 2 (fun i => (v i : ℂ)) : EuclideanSpace ℂ ι)‖ = ‖v‖ := by
  simp only [PiLp.norm_eq_of_L2, PiLp.toLp_apply, Complex.norm_real]

end
