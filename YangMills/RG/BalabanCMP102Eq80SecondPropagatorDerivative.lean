/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4V0SecondMixedLocalization

/-!
# Exact second mixed propagator derivative of equation (80)

The first equation-(80) propagator derivative depends on the current
propagator `H`, its first weakening derivative `K`, and the derivative of
`V₀` at the shifted field.  Along a second weakening coordinate these three
objects vary simultaneously.

This file proves the literal product and chain rule.  If

* `H' = L`,
* `K' = M`, and
* `(DV₀(A - H(D A)))' = -D²V₀(A - H(D A))[L(D A), ·]`,

then the derivative is exactly

* the first propagator-directional expression in direction `M`,
* the symmetric quadratic cross term between `L` and `K`, and
* the Hessian term `D²V₀[L(D A), K(D A)]`.

No symmetry of the Hessian is assumed, and no estimate is used.
-/

open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

/-- Literal second mixed equation-(80) propagator derivative. -/
noncomputable def cmp102Eq80SecondPropagatorMixedDerivative
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F)
    (H K L M : F →L[ℝ] E)
    (Δπ : E →L[ℝ] E) (J A : E)
    (V₀' : E →L[ℝ] ℝ)
    (V₀'' : E →L[ℝ] E →L[ℝ] ℝ) : ℝ :=
  cmp102Eq80PropagatorDirectionalDerivative
      D D₃ H M Δπ J A V₀'
    + cmp102Eq80QuadraticMixedPairTerm L K Δπ (D A)
    + V₀'' (L (D A)) (K (D A))

/-- Exact product/chain rule for the first propagator-directional expression
along a second real parameter. -/
theorem hasDerivAt_cmp102Eq80PropagatorDirectionalDerivative_curves
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F)
    (Hcurve Kcurve : ℝ → F →L[ℝ] E)
    (L M : F →L[ℝ] E)
    (Δπ : E →L[ℝ] E) (J A : E)
    (VprimeCurve : ℝ → E →L[ℝ] ℝ)
    (V₀'' : E →L[ℝ] E →L[ℝ] ℝ)
    (t : ℝ)
    (hH : HasDerivAt Hcurve L t)
    (hK : HasDerivAt Kcurve M t)
    (hVprime : HasDerivAt VprimeCurve
      (-(V₀'' (L (D A)))) t) :
    HasDerivAt
      (fun u =>
        cmp102Eq80PropagatorDirectionalDerivative D D₃
          (Hcurve u) (Kcurve u) Δπ J A (VprimeCurve u))
      (cmp102Eq80SecondPropagatorMixedDerivative D D₃
        (Hcurve t) (Kcurve t) L M Δπ J A
        (VprimeCurve t) V₀'') t := by
  have hHD :
      HasDerivAt (fun u => Hcurve u (D A)) (L (D A)) t := by
    simpa using hH.clm_apply (hasDerivAt_const (x := t) (D A))
  have hKD :
      HasDerivAt (fun u => Kcurve u (D A)) (M (D A)) t := by
    simpa using hK.clm_apply (hasDerivAt_const (x := t) (D A))
  have hKD₃ :
      HasDerivAt (fun u => Kcurve u (D₃ A)) (M (D₃ A)) t := by
    simpa using hK.clm_apply (hasDerivAt_const (x := t) (D₃ A))
  have hΔHD :
      HasDerivAt (fun u => Δπ (Hcurve u (D A)))
        (Δπ (L (D A))) t := by
    simpa using (hasDerivAt_const (x := t) Δπ).clm_apply hHD
  have hΔKD :
      HasDerivAt (fun u => Δπ (Kcurve u (D A)))
        (Δπ (M (D A))) t := by
    simpa using (hasDerivAt_const (x := t) Δπ).clm_apply hKD
  have hJ : HasDerivAt (fun _ : ℝ => J) 0 t :=
    hasDerivAt_const (x := t) J
  have hA : HasDerivAt (fun _ : ℝ => A) 0 t :=
    hasDerivAt_const (x := t) A
  have hfirst :
      HasDerivAt
        (fun u => -inner ℝ (Kcurve u (D₃ A)) J)
        (-inner ℝ (M (D₃ A)) J) t := by
    convert (hKD₃.inner ℝ hJ).neg using 1 <;> simp
  have hsecond :
      HasDerivAt
        (fun u => -inner ℝ A (Δπ (Kcurve u (D A))))
        (-inner ℝ A (Δπ (M (D A)))) t := by
    convert (hA.inner ℝ hΔKD).neg using 1 <;> simp
  have hquad₁ :
      HasDerivAt
        (fun u => inner ℝ (Hcurve u (D A))
          (Δπ (Kcurve u (D A))))
        (inner ℝ (L (D A)) (Δπ (Kcurve t (D A))) +
          inner ℝ (Hcurve t (D A)) (Δπ (M (D A)))) t := by
    simpa [add_comm] using hHD.inner ℝ hΔKD
  have hquad₂ :
      HasDerivAt
        (fun u => inner ℝ (Kcurve u (D A))
          (Δπ (Hcurve u (D A))))
        (inner ℝ (M (D A)) (Δπ (Hcurve t (D A))) +
          inner ℝ (Kcurve t (D A)) (Δπ (L (D A)))) t := by
    simpa [add_comm] using hKD.inner ℝ hΔHD
  have hthird :
      HasDerivAt
        (fun u => (1 / 2 : ℝ) *
          (inner ℝ (Hcurve u (D A)) (Δπ (Kcurve u (D A))) +
            inner ℝ (Kcurve u (D A)) (Δπ (Hcurve u (D A)))))
        ((1 / 2 : ℝ) *
          ((inner ℝ (L (D A)) (Δπ (Kcurve t (D A))) +
              inner ℝ (Hcurve t (D A)) (Δπ (M (D A)))) +
            (inner ℝ (M (D A)) (Δπ (Hcurve t (D A))) +
              inner ℝ (Kcurve t (D A)) (Δπ (L (D A)))))) t := by
    simpa using (hquad₁.add hquad₂).const_mul (1 / 2 : ℝ)
  have hVapply :
      HasDerivAt
        (fun u => VprimeCurve u (Kcurve u (D A)))
        ((-(V₀'' (L (D A)))) (Kcurve t (D A)) +
          VprimeCurve t (M (D A))) t := by
    simpa using hVprime.clm_apply hKD
  have hfourth :
      HasDerivAt
        (fun u => -(VprimeCurve u (Kcurve u (D A))))
        (-((-(V₀'' (L (D A)))) (Kcurve t (D A)) +
          VprimeCurve t (M (D A)))) t :=
    hVapply.neg
  have hall := ((hfirst.add hsecond).add hthird).add hfourth
  convert hall using 1
  simp only [cmp102Eq80SecondPropagatorMixedDerivative,
    cmp102Eq80PropagatorDirectionalDerivative,
    cmp102Eq80QuadraticMixedPairTerm, ContinuousLinearMap.neg_apply]
  ring

/-- The previous chain rule specialized to the actual derivative of a
`C²` potential at the shifted field.  Thus the Hessian in the resulting
formula is the literal Fréchet derivative of `fderiv V₀`, not an auxiliary
bilinear form. -/
theorem
    hasDerivAt_cmp102Eq80PropagatorDirectionalDerivative_fderivCurve
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F) (V₀ : E → ℝ)
    (Hcurve Kcurve : ℝ → F →L[ℝ] E)
    (L M : F →L[ℝ] E)
    (Δπ : E →L[ℝ] E) (J A : E)
    (t : ℝ)
    (hH : HasDerivAt Hcurve L t)
    (hK : HasDerivAt Kcurve M t)
    (hV₀ : ContDiff ℝ 2 V₀) :
    HasDerivAt
      (fun u =>
        cmp102Eq80PropagatorDirectionalDerivative D D₃
          (Hcurve u) (Kcurve u) Δπ J A
          (fderiv ℝ V₀ (A - Hcurve u (D A))))
      (cmp102Eq80SecondPropagatorMixedDerivative D D₃
        (Hcurve t) (Kcurve t) L M Δπ J A
        (fderiv ℝ V₀ (A - Hcurve t (D A)))
        (fderiv ℝ (fderiv ℝ V₀)
          (A - Hcurve t (D A)))) t := by
  have hHD :
      HasDerivAt (fun u => Hcurve u (D A)) (L (D A)) t := by
    simpa using hH.clm_apply (hasDerivAt_const (x := t) (D A))
  have hA : HasDerivAt (fun _ : ℝ => A) 0 t :=
    hasDerivAt_const (x := t) A
  have harg :
      HasDerivAt (fun u => A - Hcurve u (D A))
        (-(L (D A))) t := by
    convert hA.sub hHD using 1 <;> simp
  have hgradCont :
      ContDiff ℝ 1 (fderiv ℝ V₀) :=
    hV₀.fderiv_right (m := 1) (by norm_num)
  have hgradDiff :
      Differentiable ℝ (fderiv ℝ V₀) :=
    hgradCont.differentiable one_ne_zero
  have hVprimeRaw :=
    (hgradDiff (A - Hcurve t (D A))).hasFDerivAt.comp_hasDerivAt
      t harg
  have hVprime :
      HasDerivAt
        (fun u => fderiv ℝ V₀ (A - Hcurve u (D A)))
        (-(fderiv ℝ (fderiv ℝ V₀)
          (A - Hcurve t (D A)) (L (D A)))) t := by
    simpa using hVprimeRaw
  exact
    hasDerivAt_cmp102Eq80PropagatorDirectionalDerivative_curves
      D D₃ Hcurve Kcurve L M Δπ J A
      (fun u => fderiv ℝ V₀ (A - Hcurve u (D A)))
      (fderiv ℝ (fderiv ℝ V₀)
        (A - Hcurve t (D A)))
      t hH hK hVprime

end

end YangMills.RG
