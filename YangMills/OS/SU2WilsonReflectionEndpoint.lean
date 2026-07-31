/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/

import YangMills.OS.SU2WilsonReflectionGeometry
import YangMills.OS.SU2WilsonReflectionSharp
import YangMills.ClayCore.SchurNormOne

/-!
# Non-vacuous finite SU(2) Wilson reflection-positivity endpoint

This endpoint consumes the exact producer from
`SU2WilsonReflectionKernel` and the concrete cut from
`SU2WilsonReflectionGeometry`.  It makes no continuum, reconstruction,
mass-gap, or Clay-problem claim.
-/

noncomputable section

open Matrix Complex MeasureTheory

namespace YangMills.OS

/-- The one-crossing-plaquette OS inequality for a continuous complex
half-observable. -/
theorem su2OnePlaquette_reflection_positive
    (β : ℝ) (hβ : 0 < β) (F : SU2 → ℂ) (hF : Continuous F) :
    ∃ r : ℝ, 0 ≤ r ∧
      su2OnePlaquetteReflectedPairing β F = (r : ℂ) := by
  rw [su2OnePlaquetteReflectedPairing_eq_kernelIntegralForm]
  exact su2WilsonCrossing_isHaarPSDKernel β hβ.le F hF

/-- At the identity boundary configuration the physical crossing factor is
`e^β`, so the endpoint genuinely depends on the coupling. -/
theorem su2WilsonCrossingKernel_one_one (β : ℝ) :
    su2WilsonCrossingKernel β (1 : SU2) (1 : SU2) = Real.exp β := by
  simp [su2WilsonCrossingKernel, Matrix.trace, Matrix.diag_apply]

/-- A trace-zero SU(2) element used to witness non-constancy in the boundary
variables. -/
def su2TraceZero : SU2 :=
  YangMills.ClayCore.signedSwapSU
    (N := 2) (0 : Fin 2) (1 : Fin 2) (by decide)

theorem su2TraceZero_trace :
  Matrix.trace
      ((su2TraceZero : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  simp [su2TraceZero, YangMills.ClayCore.signedSwapSU_val,
    YangMills.ClayCore.signedSwapMat, Matrix.trace, Matrix.diag_apply,
    Fin.sum_univ_two]

theorem su2WilsonCrossingKernel_traceZero_one (β : ℝ) :
    su2WilsonCrossingKernel β su2TraceZero (1 : SU2) = 1 := by
  simp [su2WilsonCrossingKernel, su2TraceZero_trace]

/-- Strict non-vacuity: for every physical coupling `β > 0`, the crossing
kernel is not constant on SU(2) boundary data. -/
theorem su2WilsonCrossingKernel_nonconstant
    (β : ℝ) (hβ : 0 < β) :
    su2WilsonCrossingKernel β (1 : SU2) (1 : SU2) ≠
      su2WilsonCrossingKernel β su2TraceZero (1 : SU2) := by
  rw [su2WilsonCrossingKernel_one_one,
    su2WilsonCrossingKernel_traceZero_one]
  exact_mod_cast ne_of_gt (Real.one_lt_exp_iff.mpr hβ)

/-- The constant observable has a strictly positive pairing.  This rules out
the degenerate possibility that the endpoint inequality is witnessed only by
the zero quadratic form. -/
theorem su2OnePlaquette_constant_pairing_strict
    (β : ℝ) (hβ : 0 < β) :
    ∃ r : ℝ, 0 < r ∧
      su2OnePlaquetteReflectedPairing β
        (fun _ => (1 : ℂ)) = (r : ℂ) := by
  let μ : Measure SU2 := sunHaarProb 2
  let G : SU2 → ℝ := fun x =>
    ∫ y, (su2WilsonCrossingKernel β x y).re ∂μ
  have hKre_cont : Continuous (fun p : SU2 × SU2 =>
      (su2WilsonCrossingKernel β p.1 p.2).re) :=
    Complex.continuous_re.comp (su2WilsonCrossingKernel_continuous β)
  have hKre_integrable (x : SU2) :
      Integrable (fun y => (su2WilsonCrossingKernel β x y).re) μ := by
    have hc : Continuous (fun y =>
        (su2WilsonCrossingKernel β x y).re) :=
      Complex.continuous_re.comp
        (su2WilsonCrossingKernel_continuous_right β x)
    exact hc.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hG_cont : Continuous G := by
    rw [← continuousOn_univ]
    refine continuousOn_integral_of_compact_support
      (μ := μ) (s := Set.univ) (k := Set.univ) isCompact_univ ?_ ?_
    · simpa [G, Function.uncurry] using hKre_cont
    · intro p x hp hx
      simp at hx
  have hinner_lower (x : SU2) : Real.exp (-β) ≤ G x := by
    change Real.exp (-β) ≤
      ∫ y, (su2WilsonCrossingKernel β x y).re ∂μ
    calc
      Real.exp (-β) = ∫ _y : SU2, Real.exp (-β) ∂μ := by simp [μ]
      _ ≤ ∫ y, (su2WilsonCrossingKernel β x y).re ∂μ := by
        apply integral_mono (integrable_const _) (hKre_integrable x)
        intro y
        exact su2WilsonCrossingKernel_re_lower β hβ.le x y
  have houter_lower : Real.exp (-β) ≤ ∫ x, G x ∂μ := by
    calc
      Real.exp (-β) = ∫ _x : SU2, Real.exp (-β) ∂μ := by simp [μ]
      _ ≤ ∫ x, G x ∂μ := by
        apply integral_mono (integrable_const _)
          (hG_cont.integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _))
        exact hinner_lower
  have hK_integrable (x : SU2) :
      Integrable (fun y => su2WilsonCrossingKernel β x y) μ :=
    (su2WilsonCrossingKernel_continuous_right β x).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hH_cont : Continuous (fun x =>
      ∫ y, su2WilsonCrossingKernel β x y ∂μ) := by
    rw [← continuousOn_univ]
    refine continuousOn_integral_of_compact_support
      (μ := μ) (s := Set.univ) (k := Set.univ) isCompact_univ ?_ ?_
    · simpa [Function.uncurry] using
        (su2WilsonCrossingKernel_continuous β)
    · intro p x hp hx
      simp at hx
  have hH_integrable :
      Integrable (fun x => ∫ y, su2WilsonCrossingKernel β x y ∂μ) μ :=
    hH_cont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hform_re :
      (kernelIntegralForm μ (su2WilsonCrossingKernel β)
        (fun _ => (1 : ℂ))).re = ∫ x, G x ∂μ := by
    unfold kernelIntegralForm
    simp only [map_one, one_mul, mul_one]
    calc
      (∫ x, ∫ y, su2WilsonCrossingKernel β x y ∂μ ∂μ).re =
          ∫ x, (∫ y, su2WilsonCrossingKernel β x y ∂μ).re ∂μ := by
            simpa using (integral_re hH_integrable).symm
      _ = ∫ x, ∫ y, (su2WilsonCrossingKernel β x y).re ∂μ ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        simpa using (integral_re (hK_integrable x)).symm
      _ = ∫ x, G x ∂μ := by rfl
  rcases su2OnePlaquette_reflection_positive β hβ
      (fun _ => (1 : ℂ)) continuous_const with ⟨r, hr, heq⟩
  have heqKernel :
      kernelIntegralForm (sunHaarProb 2)
        (su2WilsonCrossingKernel β) (fun _ => (1 : ℂ)) = (r : ℂ) := by
    rw [← su2OnePlaquetteReflectedPairing_eq_kernelIntegralForm]
    exact heq
  refine ⟨r, ?_, heq⟩
  have hre : r = ∫ x, G x ∂μ := by
    have hreal := congrArg Complex.re heqKernel
    calc
      r = (kernelIntegralForm (sunHaarProb 2)
          (su2WilsonCrossingKernel β) (fun _ => (1 : ℂ))).re := by
        simpa using hreal.symm
      _ = ∫ x, G x ∂μ := by simpa [μ] using hform_re
  rw [hre]
  exact (Real.exp_pos (-β)).trans_le houter_lower

end YangMills.OS
