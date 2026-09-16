import YangMills.RG.BalabanCMP102Eq80PhysicalDomainFTCSecondFieldDerivative

set_option synthInstance.maxHeartbeats 400000

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]

noncomputable local instance nestedTwoNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := E →L[ℝ] ℝ)
    (σ₁₂ := RingHom.id ℝ)

noncomputable local instance nestedThreeNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E)
    (F := E →L[ℝ] (E →L[ℝ] ℝ)) (σ₁₂ := RingHom.id ℝ)

#synth Norm (E →L[ℝ] ℝ)
#synth NormedAddCommGroup (E →L[ℝ] ℝ)
#synth Norm (E →L[ℝ] (E →L[ℝ] ℝ))
#synth NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ))
#synth Nontrivial (E →L[ℝ] (E →L[ℝ] ℝ))
#synth NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ))
#synth Norm (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)))
#synth NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)))
