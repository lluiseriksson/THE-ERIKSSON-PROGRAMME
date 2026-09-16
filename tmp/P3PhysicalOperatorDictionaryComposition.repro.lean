import Mathlib

/-!
PRE-VALIDATION MINIMAL REPRODUCER: this file isolates the pointwise
composition rewrite used by the P3 physical operator dictionary.  It imports
no project declaration and is not compiler evidence for the physical chain.
-/

noncomputable section

variable {X Y Z W O : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [NormedAddCommGroup O] [NormedSpace ℝ O]

/-- A pointwise tower equality and a pointwise adjoint factorization transport
through the common scalar and the two operator compositions. -/
example
    (c : ℝ) (Qr : X →L[ℝ] Y) (nextAverage : Y →L[ℝ] Z)
    (Qn : X →L[ℝ] Z) (stepAdjoint : Z →L[ℝ] W)
    (currentAdjoint : W →L[ℝ] O) (nextAdjoint : Z →L[ℝ] O)
    (hQ : Qn = nextAverage.comp Qr)
    (hAdjoint : ∀ eta, nextAdjoint eta = currentAdjoint (stepAdjoint eta)) :
    c • ((currentAdjoint.comp stepAdjoint).comp (nextAverage.comp Qr)) =
      c • (nextAdjoint.comp Qn) := by
  apply ContinuousLinearMap.ext
  intro eta
  have hQeta := congrArg (fun Q => Q eta) hQ
  simp only [ContinuousLinearMap.comp_apply] at hQeta
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply]
  rw [hQeta]
  exact congrArg (fun z => c • z) (hAdjoint _).symm

end
