/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PropagatorDerivative

/-!
# Summable propagator directions in CMP102 equation (80)

For a fixed base propagator, field and derivative of `V₀`, the literal
equation-(80) directional derivative is a continuous linear functional of
the propagator direction. This permits a convergent walk expansion to be
inserted inside one exact nonlinear minimizer increment without
rearranging the outer ordered telescoping series.
-/

open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

/-- The literal equation-(80) propagator derivative, packaged as a
continuous linear functional of its direction. -/
noncomputable def cmp102Eq80PropagatorDirectionalDerivativeCLM
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F)
    (H : F →L[ℝ] E) (Δπ : E →L[ℝ] E) (J A : E)
    (V₀' : E →L[ℝ] ℝ) :
    (F →L[ℝ] E) →L[ℝ] ℝ := by
  let L : (F →L[ℝ] E) →ₗ[ℝ] ℝ := {
    toFun := fun K =>
      cmp102Eq80PropagatorDirectionalDerivative
        D D₃ H K Δπ J A V₀'
    map_add' := fun K₁ K₂ => by
      simp only [cmp102Eq80PropagatorDirectionalDerivative,
        ContinuousLinearMap.add_apply, map_add,
        inner_add_left, inner_add_right]
      ring
    map_smul' := fun r K => by
      simp [cmp102Eq80PropagatorDirectionalDerivative,
        ContinuousLinearMap.smul_apply, map_smul,
        inner_smul_left, inner_smul_right]
      ring
  }
  have hcontinuous : Continuous fun K : F →L[ℝ] E =>
      cmp102Eq80PropagatorDirectionalDerivative
        D D₃ H K Δπ J A V₀' := by
    unfold cmp102Eq80PropagatorDirectionalDerivative
    fun_prop
  exact ContinuousLinearMap.mk L hcontinuous

@[simp]
theorem cmp102Eq80PropagatorDirectionalDerivativeCLM_apply
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F)
    (H K : F →L[ℝ] E) (Δπ : E →L[ℝ] E) (J A : E)
    (V₀' : E →L[ℝ] ℝ) :
    cmp102Eq80PropagatorDirectionalDerivativeCLM
        D D₃ H Δπ J A V₀' K =
      cmp102Eq80PropagatorDirectionalDerivative
        D D₃ H K Δπ J A V₀' :=
  rfl

/-- A summable family of propagator directions remains summable after
applying the literal equation-(80) derivative. -/
theorem summable_cmp102Eq80PropagatorDirectionalDerivative
    {E F ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F)
    (H : F →L[ℝ] E) (K : ι → F →L[ℝ] E)
    (Δπ : E →L[ℝ] E) (J A : E)
    (V₀' : E →L[ℝ] ℝ) (hK : Summable K) :
    Summable fun i =>
      cmp102Eq80PropagatorDirectionalDerivative
        D D₃ H (K i) Δπ J A V₀' := by
  simpa only [Function.comp_apply,
    cmp102Eq80PropagatorDirectionalDerivativeCLM_apply] using
    hK.map
      (cmp102Eq80PropagatorDirectionalDerivativeCLM
        D D₃ H Δπ J A V₀')
      (cmp102Eq80PropagatorDirectionalDerivativeCLM
        D D₃ H Δπ J A V₀').continuous

/-- The literal equation-(80) derivative commutes with every genuinely
summable propagator-direction series. -/
theorem cmp102Eq80PropagatorDirectionalDerivative_tsum
    {E F ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F)
    (H : F →L[ℝ] E) (K : ι → F →L[ℝ] E)
    (Δπ : E →L[ℝ] E) (J A : E)
    (V₀' : E →L[ℝ] ℝ) (hK : Summable K) :
    cmp102Eq80PropagatorDirectionalDerivative
        D D₃ H (∑' i, K i) Δπ J A V₀' =
      ∑' i,
        cmp102Eq80PropagatorDirectionalDerivative
          D D₃ H (K i) Δπ J A V₀' := by
  exact
    (cmp102Eq80PropagatorDirectionalDerivativeCLM
      D D₃ H Δπ J A V₀').map_tsum hK

end

end YangMills.RG
