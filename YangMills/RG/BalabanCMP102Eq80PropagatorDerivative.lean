/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import YangMills.RG.BalabanCMP102Eq80GlobalPotential

/-!
# Exact propagator derivative of the CMP102 equation-(80) potential

For a fixed physical field, equation (80) is a nonlinear functional of its
propagator `H`.  This file differentiates the literal affine line
`H + t K` term by term.  In particular, the contribution from
`V₀(A - H D(A))` is the Fréchet derivative of the actual `V₀` at the actual
shifted field, applied to `-K D(A)`.

No bound or synthetic potential is introduced.  This is the chain-rule bridge
needed before the source weakening derivatives can be inserted into the
iterated FTC expansion of the full CMP102 potential.
-/

open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

/-- Directional derivative of the literal equation-(80) potential with
respect to its propagator. -/
noncomputable def cmp102Eq80PropagatorDirectionalDerivative
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F)
    (H K : F →L[ℝ] E) (Δπ : E →L[ℝ] E) (J A : E)
    (V₀' : E →L[ℝ] ℝ) : ℝ :=
  - inner ℝ (K (D₃ A)) J
  - inner ℝ A (Δπ (K (D A)))
  + (1 / 2 : ℝ) *
      (inner ℝ (H (D A)) (Δπ (K (D A))) +
        inner ℝ (K (D A)) (Δπ (H (D A))))
  - V₀' (K (D A))

/-- Continuity of the literal propagator-directional derivative along a
continuous propagator curve and a continuously varying derivative of `V₀`. -/
theorem continuous_cmp102Eq80PropagatorDirectionalDerivative
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F) (V₀ : E → ℝ)
    (Hcurve : ℝ → F →L[ℝ] E) (K : F →L[ℝ] E)
    (Δπ : E →L[ℝ] E) (J A : E)
    (hH : Continuous Hcurve)
    (hV₀ : Continuous (fderiv ℝ V₀)) :
    Continuous fun t =>
      cmp102Eq80PropagatorDirectionalDerivative D D₃
        (Hcurve t) K Δπ J A
        (fderiv ℝ V₀ (A - Hcurve t (D A))) := by
  have hHD : Continuous fun t => Hcurve t (D A) :=
    hH.clm_apply continuous_const
  have hVarg : Continuous fun t => A - Hcurve t (D A) :=
    continuous_const.sub hHD
  have hVderiv :
      Continuous fun t => fderiv ℝ V₀ (A - Hcurve t (D A)) :=
    hV₀.comp hVarg
  have hVapply :
      Continuous fun t =>
        fderiv ℝ V₀ (A - Hcurve t (D A)) (K (D A)) :=
    hVderiv.clm_apply continuous_const
  have hΔHD : Continuous fun t => Δπ (Hcurve t (D A)) :=
    continuous_const.clm_apply hHD
  unfold cmp102Eq80PropagatorDirectionalDerivative
  fun_prop

private theorem hasDerivAt_affineCLM_apply
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H K : F →L[ℝ] E) (v : F) (t : ℝ) :
    HasDerivAt (fun u : ℝ => (H + u • K) v) (K v) t := by
  convert
    (hasDerivAt_const (x := t) (H v)).add
      ((hasDerivAt_id (𝕜 := ℝ) t).smul_const (K v)) using 1 <;>
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      Pi.add_apply, Pi.smul_apply, one_smul, zero_add]

/-- Exact chain rule along the affine propagator line `H + t K`. -/
theorem hasDerivAt_cmp102Eq80GlobalPotential_affinePropagator
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F) (V₀ : E → ℝ)
    (H K : F →L[ℝ] E) (Δπ : E →L[ℝ] E) (J A : E)
    (t : ℝ) (V₀' : E →L[ℝ] ℝ)
    (hV₀ : HasFDerivAt V₀ V₀'
      (A - (H + t • K) (D A))) :
    HasDerivAt
      (fun u : ℝ =>
        cmp102Eq80GlobalPotential D D₃ V₀ (H + u • K) Δπ J A)
      (cmp102Eq80PropagatorDirectionalDerivative
        D D₃ (H + t • K) K Δπ J A V₀') t := by
  have hHD₃ := hasDerivAt_affineCLM_apply H K (D₃ A) t
  have hHD := hasDerivAt_affineCLM_apply H K (D A) t
  have hJ : HasDerivAt (fun _ : ℝ => J) 0 t :=
    hasDerivAt_const (x := t) J
  have hA : HasDerivAt (fun _ : ℝ => A) 0 t :=
    hasDerivAt_const (x := t) A
  have hΔHD : HasDerivAt
      (fun u : ℝ => Δπ ((H + u • K) (D A)))
      (Δπ (K (D A))) t :=
    by
      convert
        (hasDerivAt_const (x := t) (Δπ (H (D A)))).add
          ((hasDerivAt_id (𝕜 := ℝ) t).smul_const
            (Δπ (K (D A)))) using 1
      · funext u
        simp
      · simp
  have hfirst : HasDerivAt
      (fun u : ℝ => - inner ℝ ((H + u • K) (D₃ A)) J)
      (- inner ℝ (K (D₃ A)) J) t := by
    convert (hHD₃.inner ℝ hJ).neg using 1 <;> simp
  have hsecond : HasDerivAt
      (fun u : ℝ =>
        - inner ℝ A (Δπ ((H + u • K) (D A))))
      (- inner ℝ A (Δπ (K (D A)))) t := by
    convert (hA.inner ℝ hΔHD).neg using 1 <;> simp
  have hthirdInner : HasDerivAt
      (fun u : ℝ =>
        inner ℝ ((H + u • K) (D A))
          (Δπ ((H + u • K) (D A))))
      (inner ℝ ((H + t • K) (D A)) (Δπ (K (D A))) +
        inner ℝ (K (D A)) (Δπ ((H + t • K) (D A)))) t := by
    convert hHD.inner ℝ hΔHD using 1 <;> simp
  have hthird : HasDerivAt
      (fun u : ℝ =>
        (1 / 2 : ℝ) *
          inner ℝ ((H + u • K) (D A))
            (Δπ ((H + u • K) (D A))))
      ((1 / 2 : ℝ) *
        (inner ℝ ((H + t • K) (D A)) (Δπ (K (D A))) +
          inner ℝ (K (D A)) (Δπ ((H + t • K) (D A))))) t := by
    simpa using hthirdInner.const_mul (1 / 2 : ℝ)
  have harg : HasDerivAt
      (fun u : ℝ => A - (H + u • K) (D A))
      (-(K (D A))) t := by
    convert hA.sub hHD using 1 <;> simp
  have hfourth : HasDerivAt
      (fun u : ℝ => V₀ (A - (H + u • K) (D A)))
      (V₀' (-(K (D A)))) t := by
    convert (hV₀.comp t harg).hasDerivAt using 1 <;>
      simp [Function.comp_def]
  have hall := ((hfirst.add hsecond).add hthird).add hfourth
  simpa [cmp102Eq80GlobalPotential,
    cmp102Eq80PropagatorDirectionalDerivative, map_neg, sub_eq_add_neg,
    add_assoc] using hall

/-- Exact chain rule for the literal equation-(80) potential along an
arbitrary differentiable propagator curve.  This is the form consumed by the
physical mixed weakening recurrence. -/
theorem hasDerivAt_cmp102Eq80GlobalPotential_propagatorCurve
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F) (V₀ : E → ℝ)
    (Hcurve : ℝ → F →L[ℝ] E) (K : F →L[ℝ] E)
    (Δπ : E →L[ℝ] E) (J A : E)
    (t : ℝ)
    (hH : HasDerivAt Hcurve K t)
    (V₀' : E →L[ℝ] ℝ)
    (hV₀ : HasFDerivAt V₀ V₀'
      (A - Hcurve t (D A))) :
    HasDerivAt
      (fun u : ℝ =>
        cmp102Eq80GlobalPotential D D₃ V₀ (Hcurve u) Δπ J A)
      (cmp102Eq80PropagatorDirectionalDerivative
        D D₃ (Hcurve t) K Δπ J A V₀') t := by
  have hHD₃ : HasDerivAt (fun u => Hcurve u (D₃ A)) (K (D₃ A)) t := by
    simpa using hH.clm_apply (hasDerivAt_const (x := t) (D₃ A))
  have hHD : HasDerivAt (fun u => Hcurve u (D A)) (K (D A)) t := by
    simpa using hH.clm_apply (hasDerivAt_const (x := t) (D A))
  have hJ : HasDerivAt (fun _ : ℝ => J) 0 t :=
    hasDerivAt_const (x := t) J
  have hA : HasDerivAt (fun _ : ℝ => A) 0 t :=
    hasDerivAt_const (x := t) A
  have hΔHD : HasDerivAt
      (fun u : ℝ => Δπ (Hcurve u (D A)))
      (Δπ (K (D A))) t := by
    simpa using
      (hasDerivAt_const (x := t) Δπ).clm_apply hHD
  have hfirst : HasDerivAt
      (fun u : ℝ => - inner ℝ (Hcurve u (D₃ A)) J)
      (- inner ℝ (K (D₃ A)) J) t := by
    convert (hHD₃.inner ℝ hJ).neg using 1 <;> simp
  have hsecond : HasDerivAt
      (fun u : ℝ => - inner ℝ A (Δπ (Hcurve u (D A))))
      (- inner ℝ A (Δπ (K (D A)))) t := by
    convert (hA.inner ℝ hΔHD).neg using 1 <;> simp
  have hthirdInner : HasDerivAt
      (fun u : ℝ =>
        inner ℝ (Hcurve u (D A)) (Δπ (Hcurve u (D A))))
      (inner ℝ (Hcurve t (D A)) (Δπ (K (D A))) +
        inner ℝ (K (D A)) (Δπ (Hcurve t (D A)))) t := by
    convert hHD.inner ℝ hΔHD using 1 <;> simp
  have hthird : HasDerivAt
      (fun u : ℝ =>
        (1 / 2 : ℝ) *
          inner ℝ (Hcurve u (D A)) (Δπ (Hcurve u (D A))))
      ((1 / 2 : ℝ) *
        (inner ℝ (Hcurve t (D A)) (Δπ (K (D A))) +
          inner ℝ (K (D A)) (Δπ (Hcurve t (D A))))) t := by
    simpa using hthirdInner.const_mul (1 / 2 : ℝ)
  have harg : HasDerivAt
      (fun u : ℝ => A - Hcurve u (D A))
      (-(K (D A))) t := by
    convert hA.sub hHD using 1 <;> simp
  have hfourth : HasDerivAt
      (fun u : ℝ => V₀ (A - Hcurve u (D A)))
      (V₀' (-(K (D A)))) t := by
    convert (hV₀.comp t harg).hasDerivAt using 1 <;>
      simp [Function.comp_def]
  have hall := ((hfirst.add hsecond).add hthird).add hfourth
  simpa [cmp102Eq80GlobalPotential,
    cmp102Eq80PropagatorDirectionalDerivative, map_neg, sub_eq_add_neg,
    add_assoc] using hall

end

end YangMills.RG
