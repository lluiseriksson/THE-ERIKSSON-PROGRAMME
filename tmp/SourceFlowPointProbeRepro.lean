import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# PRE-VALIDATION: point-probe carrier transport, Mathlib-only repro

Source present; .olean not materialized; result not compiler-verified.
Run before the physical point-probe draft; no project imports.
-/

noncomputable section

example {ι κ ξ : Type*} [Fintype ι] [Fintype κ] [Fintype ξ]
    [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (source : ι) (v : EuclideanSpace ℂ ξ) :
    ContinuousLinearEquiv.piCongrLeft ℂ
        (fun _ : κ => EuclideanSpace ℂ ξ) e
        (fun x => if x = source then v else 0) =
      (fun y => if y = e source then v else 0) := by
  funext y
  obtain ⟨x, hx⟩ := e.surjective y
  rw [← hx]
  have heval (f : ι → EuclideanSpace ℂ ξ) :
      ContinuousLinearEquiv.piCongrLeft ℂ
        (fun _ : κ => EuclideanSpace ℂ ξ) e f (e x) = f x := by
    simp [ContinuousLinearEquiv.piCongrLeft,
      Homeomorph.piCongrLeft, Equiv.piCongrLeft]
  rw [heval]
  simp only [e.injective.eq_iff]

example {ι ξ : Type*} [Fintype ι] [Fintype ξ] [DecidableEq ι]
    (source target : ι) (v : EuclideanSpace ℝ ξ) :
    (WithLp.toLp 2 (fun k : ξ =>
        (((if target = source then v else 0) : EuclideanSpace ℝ ξ) k : ℂ)) :
      EuclideanSpace ℂ ξ) =
      if target = source then
        (WithLp.toLp 2 fun k : ξ => (v k : ℂ)) else 0 := by
  apply PiLp.ext
  intro k
  by_cases h : target = source
  · subst target
    simp
  · simp [h]

end
