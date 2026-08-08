/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Compact
import YangMills.RG.BalabanCMP102Eq80PropagatorDerivativeDirectionSeries

/-!
# Uniform equation-(80) derivative on the radial FTC segment

The literal equation-(80) derivative is linear in the propagator
direction.  Along the compact affine radial segment its operator norm has
a uniform bound.  Consequently, any absolutely summable family of
propagator directions gives a summable family of restricted continuous
scalar functions, exactly the hypothesis used by the interval-integral
`tsum` theorem.
-/

open scoped RealInnerProductSpace
open TopologicalSpace

namespace YangMills.RG

noncomputable section

/-- The equation-(80) derivative functional along an affine propagator
line. -/
noncomputable def cmp102Eq80AffinePropagatorDirectionalDerivativeCLM
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F)
    (V₀ : E → ℝ)
    (P T : F →L[ℝ] E)
    (Δπ : E →L[ℝ] E)
    (J A : E)
    (t : ℝ) :
    (F →L[ℝ] E) →L[ℝ] ℝ :=
  cmp102Eq80PropagatorDirectionalDerivativeCLM
    D D₃ (P + t • T) Δπ J A
    (fderiv ℝ V₀ (A - (P + t • T) (D A)))

/-- Explicit coefficient controlling the equation-(80) derivative in its
propagator direction. -/
noncomputable def cmp102Eq80PropagatorDirectionalDerivativeBound
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F)
    (H : F →L[ℝ] E) (Δπ : E →L[ℝ] E)
    (J A : E) (V₀' : E →L[ℝ] ℝ) : ℝ :=
  ‖D₃ A‖ * ‖J‖ +
  ‖A‖ * (‖Δπ‖ * ‖D A‖) +
  ‖H‖ * ‖D A‖ * (‖Δπ‖ * ‖D A‖) +
  ‖V₀'‖ * ‖D A‖

/-- The explicit coefficient bounds the literal derivative linearly in
the norm of the propagator direction. -/
theorem norm_cmp102Eq80PropagatorDirectionalDerivative_le
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F)
    (H K : F →L[ℝ] E) (Δπ : E →L[ℝ] E)
    (J A : E) (V₀' : E →L[ℝ] ℝ) :
    ‖cmp102Eq80PropagatorDirectionalDerivative
        D D₃ H K Δπ J A V₀'‖ ≤
      cmp102Eq80PropagatorDirectionalDerivativeBound
        D D₃ H Δπ J A V₀' * ‖K‖ := by
  have hKD₃ : ‖K (D₃ A)‖ ≤ ‖K‖ * ‖D₃ A‖ := K.le_opNorm _
  have hKD : ‖K (D A)‖ ≤ ‖K‖ * ‖D A‖ := K.le_opNorm _
  have hHD : ‖H (D A)‖ ≤ ‖H‖ * ‖D A‖ := H.le_opNorm _
  have hΔKD : ‖Δπ (K (D A))‖ ≤ ‖Δπ‖ * ‖K (D A)‖ :=
    Δπ.le_opNorm _
  have hΔHD : ‖Δπ (H (D A))‖ ≤ ‖Δπ‖ * ‖H (D A)‖ :=
    Δπ.le_opNorm _
  have hV : ‖V₀' (K (D A))‖ ≤ ‖V₀'‖ * ‖K (D A)‖ :=
    V₀'.le_opNorm _
  have hΔKD' :
      ‖Δπ (K (D A))‖ ≤ ‖Δπ‖ * (‖K‖ * ‖D A‖) :=
    hΔKD.trans
      (mul_le_mul_of_nonneg_left hKD (norm_nonneg Δπ))
  have hΔHD' :
      ‖Δπ (H (D A))‖ ≤ ‖Δπ‖ * (‖H‖ * ‖D A‖) :=
    hΔHD.trans
      (mul_le_mul_of_nonneg_left hHD (norm_nonneg Δπ))
  unfold cmp102Eq80PropagatorDirectionalDerivative
  unfold cmp102Eq80PropagatorDirectionalDerivativeBound
  calc
    ‖-inner ℝ (K (D₃ A)) J
        - inner ℝ A (Δπ (K (D A)))
        + (1 / 2 : ℝ) *
            (inner ℝ (H (D A)) (Δπ (K (D A))) +
              inner ℝ (K (D A)) (Δπ (H (D A))))
        - V₀' (K (D A))‖
        ≤
          ‖inner ℝ (K (D₃ A)) J‖ +
          ‖inner ℝ A (Δπ (K (D A)))‖ +
          (1 / 2 : ℝ) *
            (‖inner ℝ (H (D A)) (Δπ (K (D A)))‖ +
             ‖inner ℝ (K (D A)) (Δπ (H (D A)))‖) +
          ‖V₀' (K (D A))‖ := by
      rw [Real.norm_eq_abs]
      calc
        |(-inner ℝ (K (D₃ A)) J
            - inner ℝ A (Δπ (K (D A)))
            + (1 / 2 : ℝ) *
                (inner ℝ (H (D A)) (Δπ (K (D A))) +
                  inner ℝ (K (D A)) (Δπ (H (D A)))))
            - V₀' (K (D A))|
            ≤
              |(-inner ℝ (K (D₃ A)) J
                - inner ℝ A (Δπ (K (D A))))
                + (1 / 2 : ℝ) *
                    (inner ℝ (H (D A)) (Δπ (K (D A))) +
                      inner ℝ (K (D A)) (Δπ (H (D A))))| +
              |V₀' (K (D A))| := abs_sub _ _
        _ ≤
              (|inner ℝ (K (D₃ A)) J| +
                |inner ℝ A (Δπ (K (D A)))|) +
              (1 / 2 : ℝ) *
                (|inner ℝ (H (D A)) (Δπ (K (D A)))| +
                  |inner ℝ (K (D A)) (Δπ (H (D A)))|) +
              |V₀' (K (D A))| := by
            have hleft :
                |(-inner ℝ (K (D₃ A)) J)
                    - inner ℝ A (Δπ (K (D A)))| ≤
                  |inner ℝ (K (D₃ A)) J| +
                    |inner ℝ A (Δπ (K (D A)))| := by
              simpa only [abs_neg] using
                abs_sub (-inner ℝ (K (D₃ A)) J)
                  (inner ℝ A (Δπ (K (D A))))
            have hright :
                |(1 / 2 : ℝ) *
                    (inner ℝ (H (D A)) (Δπ (K (D A))) +
                      inner ℝ (K (D A)) (Δπ (H (D A))))| ≤
                  (1 / 2 : ℝ) *
                    (|inner ℝ (H (D A)) (Δπ (K (D A)))| +
                      |inner ℝ (K (D A)) (Δπ (H (D A)))|) := by
              rw [abs_mul,
                abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
              exact
                mul_le_mul_of_nonneg_left (abs_add_le _ _)
                  (by norm_num)
            have houter :
                |(-inner ℝ (K (D₃ A)) J
                    - inner ℝ A (Δπ (K (D A))))
                    + (1 / 2 : ℝ) *
                        (inner ℝ (H (D A)) (Δπ (K (D A))) +
                          inner ℝ (K (D A)) (Δπ (H (D A))))| ≤
                  |(-inner ℝ (K (D₃ A)) J)
                    - inner ℝ A (Δπ (K (D A)))| +
                  |(1 / 2 : ℝ) *
                    (inner ℝ (H (D A)) (Δπ (K (D A))) +
                      inner ℝ (K (D A)) (Δπ (H (D A))))| :=
              abs_add_le _ _
            exact
              add_le_add
                (houter.trans (add_le_add hleft hright))
                (le_refl _)
        _ = _ := by simp only [Real.norm_eq_abs]
    _ ≤
          (‖K (D₃ A)‖ * ‖J‖) +
          (‖A‖ * ‖Δπ (K (D A))‖) +
          (1 / 2 : ℝ) *
            ((‖H (D A)‖ * ‖Δπ (K (D A))‖) +
             (‖K (D A)‖ * ‖Δπ (H (D A))‖)) +
          ‖V₀'‖ * ‖K (D A)‖ := by
      gcongr <;> apply abs_real_inner_le_norm
    _ ≤
          (‖K‖ * ‖D₃ A‖) * ‖J‖ +
          ‖A‖ * (‖Δπ‖ * (‖K‖ * ‖D A‖)) +
          (1 / 2 : ℝ) *
            (((‖H‖ * ‖D A‖) *
                (‖Δπ‖ * (‖K‖ * ‖D A‖))) +
             ((‖K‖ * ‖D A‖) *
                (‖Δπ‖ * (‖H‖ * ‖D A‖)))) +
          ‖V₀'‖ * (‖K‖ * ‖D A‖) := by
      gcongr
    _ =
          ((‖D₃ A‖ * ‖J‖ +
            ‖A‖ * (‖Δπ‖ * ‖D A‖) +
            ‖H‖ * ‖D A‖ * (‖Δπ‖ * ‖D A‖) +
            ‖V₀'‖ * ‖D A‖) * ‖K‖) := by
      ring
    _ = _ := rfl

/-- Along the radial segment, the explicit derivative coefficient has a
uniform nonnegative bound. -/
theorem
    exists_uniform_bound_cmp102Eq80AffinePropagatorDirectionalDerivative
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F)
    (V₀ : E → ℝ)
    (P T : F →L[ℝ] E)
    (Δπ : E →L[ℝ] E)
    (J A : E)
    (hV₀ : ContDiff ℝ 1 V₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      cmp102Eq80PropagatorDirectionalDerivativeBound
        D D₃ (P + t • T) Δπ J A
          (fderiv ℝ V₀ (A - (P + t • T) (D A))) ≤ C := by
  have hcoeff : Continuous fun t : ℝ =>
      cmp102Eq80PropagatorDirectionalDerivativeBound
        D D₃ (P + t • T) Δπ J A
          (fderiv ℝ V₀ (A - (P + t • T) (D A))) := by
    have hfderiv : Continuous (fderiv ℝ V₀) :=
      hV₀.continuous_fderiv one_ne_zero
    unfold cmp102Eq80PropagatorDirectionalDerivativeBound
    fun_prop
  obtain ⟨C, hC⟩ :=
    isCompact_uIcc.exists_bound_of_continuousOn hcoeff.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht
  have hnonneg :
      0 ≤ cmp102Eq80PropagatorDirectionalDerivativeBound
        D D₃ (P + t • T) Δπ J A
          (fderiv ℝ V₀ (A - (P + t • T) (D A))) := by
    unfold cmp102Eq80PropagatorDirectionalDerivativeBound
    positivity
  exact
    (le_trans (le_abs_self _)
      (by simpa [Real.norm_eq_abs] using hC t ht)).trans
      (le_max_left _ _)

/-- An absolutely summable family of propagator directions remains
summable in the compact-open sup norm after insertion into the affine
equation-(80) derivative. -/
theorem
    summable_norm_restrict_cmp102Eq80AffinePropagatorDirectionalDerivative
    {E F ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F)
    (V₀ : E → ℝ)
    (P T : F →L[ℝ] E)
    (Δπ : E →L[ℝ] E)
    (J A : E)
    (direction : ι → (F →L[ℝ] E))
    (hdirection : Summable fun i => ‖direction i‖)
    (hV₀ : ContDiff ℝ 1 V₀) :
    Summable fun i : ι =>
      ‖((⟨fun t : ℝ =>
          cmp102Eq80AffinePropagatorDirectionalDerivativeCLM
            D D₃ V₀ P T Δπ J A t (direction i),
        continuous_cmp102Eq80PropagatorDirectionalDerivative
          D D₃ V₀ (fun t : ℝ => P + t • T) (direction i)
          Δπ J A (by fun_prop)
          (hV₀.continuous_fderiv one_ne_zero)⟩ : C(ℝ, ℝ)).restrict
        (⟨Set.uIcc (0 : ℝ) 1, isCompact_uIcc⟩ : Compacts ℝ))‖ := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_uniform_bound_cmp102Eq80AffinePropagatorDirectionalDerivative
      D D₃ V₀ P T Δπ J A hV₀
  apply
    (hdirection.mul_left C).of_nonneg_of_le
      (fun _ => norm_nonneg _)
  intro i
  apply
    (ContinuousMap.norm_le (f := _)
      (mul_nonneg hC0 (norm_nonneg _))).2
  intro t
  calc
    ‖cmp102Eq80AffinePropagatorDirectionalDerivativeCLM
        D D₃ V₀ P T Δπ J A t (direction i)‖
        ≤ cmp102Eq80PropagatorDirectionalDerivativeBound
            D D₃ (P + t • T) Δπ J A
              (fderiv ℝ V₀ (A - (P + t • T) (D A))) *
            ‖direction i‖ := by
      exact
        norm_cmp102Eq80PropagatorDirectionalDerivative_le
          D D₃ (P + t • T) (direction i) Δπ J A
            (fderiv ℝ V₀ (A - (P + t • T) (D A)))
    _ ≤ C * ‖direction i‖ := by
      exact mul_le_mul_of_nonneg_right (hC t t.property) (norm_nonneg _)

end

end YangMills.RG
