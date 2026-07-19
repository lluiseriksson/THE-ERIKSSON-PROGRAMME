import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.Normed.Group.Continuity

/-!
# Radial Taylor identity for the CMP116 quadratic operator

The quadratic operator in Balaban's decomposition must not be identified with
the Hessian at the endpoint field.  For a twice continuously differentiable
real functional `f`, the exact second-order Taylor remainder is the radial
average

`integral t in 0..1, (1 - t) * D^2 f(t B)[B,B]`.

This file proves the identity in an arbitrary real normed space and packages
its diagonal value as `cmp116RadialTaylorQuadratic`.  If `f 0 = 0` and
`Df(0) = 0`, the result is the source-faithful normalization

`f B = (1 / 2) * cmp116RadialTaylorQuadratic f B`.

Honest scope: this module closes the scalar radial Taylor identity.  Packaging
the averaged bilinear form as a continuous operator `Q_f(B)`, proving its
support, and identifying the literal CMP116 activity with that construction
remain separate downstream steps.
-/

open MeasureTheory Set
open scoped Interval

namespace YangMills.RG

noncomputable section

/-- One-dimensional second-order Taylor formula with integral remainder on
the unit interval. -/
theorem cmp116TaylorIntegral_oneDim
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

/-- The Fréchet Hessian, represented as a nested continuous linear map. -/
noncomputable def cmp116FDerivHessian
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ f) x

/-- Derivative of the restriction of `f` to the radial line through `B`. -/
theorem hasDerivAt_cmp116Radial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (s • B)) (fderiv ℝ f (t • B) B) t := by
  have hline : HasDerivAt (fun s : ℝ => s • B) B t := by
    simpa using (hasDerivAt_id t).smul_const B
  have hfat : HasFDerivAt f (fderiv ℝ f (t • B)) (t • B) :=
    (hf.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable_one
      |>.differentiableAt.hasFDerivAt
  simpa [Function.comp_def] using hfat.comp_hasDerivAt t hline

/-- The second radial derivative is the Hessian evaluated twice on `B`. -/
theorem hasDerivAt_cmp116RadialFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => fderiv ℝ f (s • B) B)
      (cmp116FDerivHessian f (t • B) B B) t := by
  have hline : HasDerivAt (fun s : ℝ => s • B) B t := by
    simpa using (hasDerivAt_id t).smul_const B
  have hfderivCont : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right (by norm_num)
  have hhess : HasFDerivAt (fderiv ℝ f)
      (cmp116FDerivHessian f (t • B)) (t • B) :=
    hfderivCont.differentiable_one.differentiableAt.hasFDerivAt
  have heval : HasFDerivAt
      (fun x : E => fderiv ℝ f x B)
      ((ContinuousLinearMap.apply ℝ ℝ B).comp
        (cmp116FDerivHessian f (t • B))) (t • B) := by
    simpa [Function.comp_def] using
      (ContinuousLinearMap.apply ℝ ℝ B).hasFDerivAt.comp (t • B) hhess
  simpa [Function.comp_def, cmp116FDerivHessian] using
    heval.comp_hasDerivAt t hline

/-- Exact radial Taylor formula in a real normed space. -/
theorem cmp116TaylorIntegral_radial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f) :
    f B = f 0 + fderiv ℝ f 0 B +
      ∫ t in (0 : ℝ)..1,
        (1 - t) * cmp116FDerivHessian f (t • B) B B := by
  let g : ℝ → ℝ := fun t => f (t • B)
  let g' : ℝ → ℝ := fun t => fderiv ℝ f (t • B) B
  let g'' : ℝ → ℝ := fun t => cmp116FDerivHessian f (t • B) B B
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
  have h := cmp116TaylorIntegral_oneDim g g' g''
    (fun t ht => hasDerivAt_cmp116Radial f B hf t)
    (fun t ht => hasDerivAt_cmp116RadialFDeriv f B hf t)
    (hg'Cont.intervalIntegrable 0 1) (hg''Cont.intervalIntegrable 0 1)
  simpa [g, g', g''] using h

/-- Diagonal quadratic value of the radial Hessian average.  The factor `2`
is the CMP116 normalization for `f(B) = (1/2) <B,Q_f(B)B>`. -/
noncomputable def cmp116RadialTaylorQuadratic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (B : E) : ℝ :=
  2 * ∫ t in (0 : ℝ)..1,
    (1 - t) * cmp116FDerivHessian f (t • B) B B

/-- The radial Taylor formula written with the CMP116 quadratic
normalization. -/
theorem cmp116RadialTaylorQuadratic_decomposition
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f) :
    f B = f 0 + fderiv ℝ f 0 B +
      (1 / 2 : ℝ) * cmp116RadialTaylorQuadratic f B := by
  rw [cmp116RadialTaylorQuadratic]
  have h := cmp116TaylorIntegral_radial f B hf
  linarith

/-- Source normalization: when the constant and linear Taylor coefficients
vanish, the activity is exactly one half of its radial quadratic value. -/
theorem cmp116RadialTaylorQuadratic_eq_of_normalized
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (B : E) (hf : ContDiff ℝ 2 f)
    (hf0 : f 0 = 0) (hdf0 : fderiv ℝ f 0 = 0) :
    f B = (1 / 2 : ℝ) * cmp116RadialTaylorQuadratic f B := by
  rw [cmp116RadialTaylorQuadratic_decomposition f B hf, hf0, hdf0]
  simp

end

end YangMills.RG
