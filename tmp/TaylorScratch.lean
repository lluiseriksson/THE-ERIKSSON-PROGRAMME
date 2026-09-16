import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.Normed.Group.Continuity
import YangMills.RG.RealBilinearRiesz

open MeasureTheory Set
open scoped Interval

namespace YangMills.RG

noncomputable section

#check NormedAddGroup.toENormedAddMonoid

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ENormedAddMonoid (E →L[ℝ] ℝ) := inferInstance

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    [ENormedAddMonoid (E →L[ℝ] E →L[ℝ] ℝ)] : True := trivial

theorem testTaylorIntegral_oneDim
    (g g' g'' : ℝ → ℝ)
    (hg : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt g (g' t) t)
    (hg' : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt g' (g'' t) t)
    (hintg' : IntervalIntegrable g' volume 0 1)
    (hintg'' : IntervalIntegrable g'' volume 0 1) :
    g 1 = g 0 + g' 0 + ∫ t in (0 : ℝ)..1, (1 - t) * g'' t := by
  have hweight : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
    intro t ht
    convert (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t) using 1 <;> ring
  have hweightDeriv : IntervalIntegrable (fun _ : ℝ => (-1 : ℝ)) volume 0 1 :=
    intervalIntegrable_const
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hweight hg' hweightDeriv hintg''
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hg hintg'
  norm_num at hibp
  rw [hftc] at hibp
  linarith

noncomputable def testFDerivHessian
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ f) x

theorem testHasDerivAt_radial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (s • B)) (fderiv ℝ f (t • B) B) t := by
  have hline : HasDerivAt (fun s : ℝ => s • B) B t := by
    simpa using (hasDerivAt_id t).smul_const B
  have hfat : HasFDerivAt f (fderiv ℝ f (t • B)) (t • B) :=
    (hf.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable_one
      |>.differentiableAt.hasFDerivAt
  simpa [Function.comp_def] using hfat.comp_hasDerivAt t hline

theorem testHasDerivAt_radialFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => fderiv ℝ f (s • B) B)
      (testFDerivHessian f (t • B) B B) t := by
  have hline : HasDerivAt (fun s : ℝ => s • B) B t := by
    simpa using (hasDerivAt_id t).smul_const B
  have hfderivCont : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right (by norm_num)
  have hhess : HasFDerivAt (fderiv ℝ f)
      (testFDerivHessian f (t • B)) (t • B) :=
    hfderivCont.differentiable_one.differentiableAt.hasFDerivAt
  have heval : HasFDerivAt
      (fun x : E => fderiv ℝ f x B)
      ((ContinuousLinearMap.apply ℝ ℝ B).comp
        (testFDerivHessian f (t • B))) (t • B) := by
    simpa [Function.comp_def] using
      (ContinuousLinearMap.apply ℝ ℝ B).hasFDerivAt.comp (t • B) hhess
  simpa [Function.comp_def, testFDerivHessian] using
    heval.comp_hasDerivAt t hline

theorem testTaylorIntegral_radial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f) :
    f B = f 0 + fderiv ℝ f 0 B +
      ∫ t in (0 : ℝ)..1,
        (1 - t) * testFDerivHessian f (t • B) B B := by
  let g : ℝ → ℝ := fun t => f (t • B)
  let g' : ℝ → ℝ := fun t => fderiv ℝ f (t • B) B
  let g'' : ℝ → ℝ := fun t => testFDerivHessian f (t • B) B B
  have hlineContinuous : Continuous (fun t : ℝ => t • B) :=
    continuous_id.smul continuous_const
  have hfderivCont : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right (by norm_num)
  have hg'Cont : Continuous g' := by
    exact (hfderivCont.continuous.clm_apply continuous_const).comp hlineContinuous
  have hhessCont : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ f)) :=
    hfderivCont.fderiv_right (by norm_num)
  have hg''Cont : Continuous g'' := by
    exact ((hhessCont.continuous.clm_apply continuous_const).clm_apply continuous_const).comp
      hlineContinuous
  have h := testTaylorIntegral_oneDim g g' g''
    (fun t ht => testHasDerivAt_radial f B hf t)
    (fun t ht => testHasDerivAt_radialFDeriv f B hf t)
    (hg'Cont.intervalIntegrable 0 1) (hg''Cont.intervalIntegrable 0 1)
  simpa [g, g', g''] using h

noncomputable def testRadialTaylorBilinear
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E]
    [CompleteSpace E]
    (f : E → ℝ) (B : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  2 • ∫ t in (0 : ℝ)..1, (1 - t) • testFDerivHessian f (t • B)

noncomputable def testRadialTaylorOperator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E]
    [CompleteSpace E]
    (f : E → ℝ) (B : E) : E →L[ℝ] E :=
  realBilinearRiesz (testRadialTaylorBilinear f B)

theorem testRadialTaylorBilinear_self
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E]
    [CompleteSpace E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f) :
    testRadialTaylorBilinear f B B B =
      2 * ∫ t in (0 : ℝ)..1,
        (1 - t) * testFDerivHessian f (t • B) B B := by
  letI : ENormedAddMonoid (E →L[ℝ] E →L[ℝ] ℝ) :=
    NormedAddGroup.toENormedAddMonoid
  have hfderivCont : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right (by norm_num)
  have hhessCont : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ f)) :=
    hfderivCont.fderiv_right (by norm_num)
  have hlineContinuous : Continuous (fun t : ℝ => t • B) :=
    continuous_id.smul continuous_const
  have hphiContinuous : Continuous
      (fun t : ℝ => (1 - t) • testFDerivHessian f (t • B)) := by
    exact (continuous_const.sub continuous_id).smul
      (hhessCont.continuous.comp hlineContinuous)
  have hphiInt : IntervalIntegrable
      (fun t : ℝ => (1 - t) • testFDerivHessian f (t • B)) volume 0 1 :=
    hphiContinuous.intervalIntegrable 0 1
  have hphiBContinuous : Continuous
      (fun t : ℝ => ((1 - t) • testFDerivHessian f (t • B)) B) :=
    hphiContinuous.clm_apply continuous_const
  have hphiBInt : IntervalIntegrable
      (fun t : ℝ => ((1 - t) • testFDerivHessian f (t • B)) B)
      volume 0 1 := hphiBContinuous.intervalIntegrable 0 1
  unfold testRadialTaylorBilinear
  rw [ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.intervalIntegral_apply hphiInt B,
    ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.intervalIntegral_apply hphiBInt B]
  simp only [smul_eq_mul, ContinuousLinearMap.smul_apply]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  simp

theorem testRadialTaylorOperator_decomposition
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E]
    [CompleteSpace E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f) :
    f B = f 0 + fderiv ℝ f 0 B +
      (1 / 2 : ℝ) * inner ℝ B (testRadialTaylorOperator f B B) := by
  have htaylor := testTaylorIntegral_radial f B hf
  have hbil := testRadialTaylorBilinear_self f B hf
  have hinner : inner ℝ B (testRadialTaylorOperator f B B) =
      testRadialTaylorBilinear f B B B := by
    rw [real_inner_comm]
    exact inner_realBilinearRiesz (testRadialTaylorBilinear f B) B B
  rw [hinner, hbil]
  linarith

end YangMills.RG
