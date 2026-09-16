import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

open MeasureTheory Set Filter
open scoped Interval

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def verticalFDeriv (F : E × ℝ → ℝ) (p : E × ℝ) : E →L[ℝ] ℝ :=
  (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)

theorem test_cont (F : E × ℝ → ℝ) (hF : ContDiff ℝ 1 F) :
    Continuous (verticalFDeriv F) := by
  unfold verticalFDeriv
  fun_prop

theorem test_parametric
    (F : E × ℝ → ℝ) (hF : ContDiff ℝ 1 F) :
    HasFDerivAt
      (fun x : E => ∫ t in (0 : ℝ)..1, F (x, t))
      (∫ t in (0 : ℝ)..1, verticalFDeriv F (0, t))
      0 := by
  have hcont : Continuous (verticalFDeriv F) := test_cont F hF
  let K : Set (E × ℝ) :=
    Metric.closedBall 0 1 ×ˢ Set.Icc (0 : ℝ) 1
  have hK : IsCompact K :=
    (isCompact_closedBall (0 : E) 1).prod
      (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))
  obtain ⟨C, hC⟩ :=
    hK.exists_bound_of_continuousOn hcont.continuousOn
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun x t => F (x, t))
      (F' := fun x t => verticalFDeriv F (x, t))
      (x₀ := (0 : E))
      (a := 0) (b := 1) (μ := volume)
      (s := Metric.closedBall (0 : E) 1)
      (bound := fun _ => C)
      (Metric.closedBall_mem_nhds _ one_pos)
  · filter_upwards []
    intro x
    exact
      ((hF.continuous.comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact
      (hF.continuous.comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  · exact hcont.comp
      (continuous_const.prodMk continuous_id) |>.aestronglyMeasurable
  · filter_upwards []
    intro t ht x hx
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact ⟨le_of_lt ht.1, ht.2⟩
    exact hC (x, t) ⟨hx, ht'⟩
  · exact intervalIntegrable_const
  · filter_upwards []
    intro t _ht x _hx
    have hpath : HasFDerivAt (fun y : E => (y, t))
        (ContinuousLinearMap.inl ℝ E ℝ) x :=
      (hasFDerivAt_id (𝕜 := ℝ) (x := x)).prodMk
        (hasFDerivAt_const (x := x) t)
    exact
      ((hF.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp
        x hpath)
