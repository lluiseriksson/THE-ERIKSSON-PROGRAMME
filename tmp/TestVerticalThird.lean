import YangMills.RG.BalabanCMP102Eq80PhysicalDomainFTCSecondFieldDerivative
import YangMills.RG.BalabanCMP102Eq80PhysicalDomainCoefficientThirdFieldDerivative

open MeasureTheory
open scoped Interval RealInnerProductSpace
open YangMills.RG

noncomputable section

variable {H E G : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

noncomputable def vderiv (F : H × E → G) (p : H × E) :
    E →L[ℝ] G :=
  (fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ H E)

example (F : H × E → G) (hF : ContDiff ℝ ⊤ F) :
    ContDiff ℝ ⊤ (vderiv F) := by
  unfold vderiv
  have hd : ContDiff ℝ ⊤ (fderiv ℝ F) :=
    hF.fderiv_right (m := ⊤) (by simp)
  fun_prop

example (F : H × E → G) (hF : ContDiff ℝ ⊤ F)
    (h : H) (x : E) :
    HasFDerivAt (fun y => F (h, y)) (vderiv F (h, x)) x := by
  exact (hF.differentiable (by simp)).differentiableAt.hasFDerivAt.comp
    x ((hasFDerivAt_const (x := x) h).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) (x := x)))

variable [Nontrivial E] [FiniteDimensional ℝ E]

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

noncomputable local instance nestedThreeNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E)
    (F := E →L[ℝ] (E →L[ℝ] ℝ)) (σ₁₂ := RingHom.id ℝ)
    (𝕜' := ℝ)

example (J : H × E → ℝ) (hJ : ContDiff ℝ ⊤ J) :
    ContDiff ℝ ⊤ (vderiv (vderiv (vderiv J))) := by
  have h1 : ContDiff ℝ ⊤ (vderiv J) := by
    unfold vderiv
    have hd := hJ.fderiv_right (m := ⊤) (by simp)
    fun_prop
  have h2 : ContDiff ℝ ⊤ (vderiv (vderiv J)) := by
    unfold vderiv
    have hd := h1.fderiv_right (m := ⊤) (by simp)
    fun_prop
  unfold vderiv
  have hd := h2.fderiv_right (m := ⊤) (by simp)
  fun_prop
