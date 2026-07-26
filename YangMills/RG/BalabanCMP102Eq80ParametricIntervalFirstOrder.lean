/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4ConnectedDomainFirstOrder
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# First derivatives through the literal FTC interval

The connected equation-(80) activities are defined by nested integrals over
the compact interval `[0, 1]`.  This file discharges the measure-theoretic
step needed to transport their first-order normalization through one such
integral.

For a jointly `C¹` integrand, finite dimensionality makes a closed
neighborhood of the origin compact.  Continuity of the vertical derivative
therefore supplies the dominated bound required by Mathlib's parametric
interval-integral theorem.  No bound on the derivative and no commutation of
derivative and integral is added as a hypothesis.
-/

namespace YangMills.RG

noncomputable section

open MeasureTheory Set Filter
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous family of field derivatives may be integrated over the
literal FTC interval.  No differentiability in the interval parameter is
required.  This is the form used by the physical weakening series, whose
parameter dependence is obtained by uniform convergence. -/
theorem hasFDerivAt_intervalIntegral_of_continuous_fieldDerivative
    [FiniteDimensional ℝ E]
    (F : E × ℝ → ℝ) (F' : E × ℝ → E →L[ℝ] ℝ)
    (hF : Continuous F) (hF' : Continuous F')
    (hdiff : ∀ x t,
      HasFDerivAt (fun y : E => F (y, t)) (F' (x, t)) x) :
    HasFDerivAt
      (fun x : E => ∫ t in (0 : ℝ)..1, F (x, t))
      (∫ t in (0 : ℝ)..1, F' (0, t))
      0 := by
  let K : Set (E × ℝ) :=
    Metric.closedBall 0 1 ×ˢ Set.Icc (0 : ℝ) 1
  have hK : IsCompact K :=
    (isCompact_closedBall (0 : E) 1).prod
      (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))
  obtain ⟨C, hC⟩ :=
    hK.exists_bound_of_continuousOn hF'.continuousOn
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun x t => F (x, t))
      (F' := fun x t => F' (x, t))
      (x₀ := (0 : E))
      (a := 0) (b := 1) (μ := volume)
      (s := Metric.closedBall (0 : E) 1)
      (bound := fun _ => C)
      (Metric.closedBall_mem_nhds _ one_pos)
  · filter_upwards []
    intro x
    exact
      ((hF.comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact
      (hF.comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  · exact hF'.comp
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
    exact hdiff x t

/-- The derivative of a joint function in its first variable. -/
noncomputable def cmp102VerticalFDeriv
    (F : E × ℝ → ℝ) (p : E × ℝ) : E →L[ℝ] ℝ :=
  (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)

/-- A jointly `C¹` real integrand may be differentiated under the literal
FTC interval.  The dominating constant is produced internally from
compactness, rather than exposed in the theorem interface. -/
theorem hasFDerivAt_intervalIntegral_of_contDiff
    [FiniteDimensional ℝ E]
    (F : E × ℝ → ℝ) (hF : ContDiff ℝ 1 F) :
    HasFDerivAt
      (fun x : E => ∫ t in (0 : ℝ)..1, F (x, t))
      (∫ t in (0 : ℝ)..1, cmp102VerticalFDeriv F (0, t))
      0 := by
  have hcont : Continuous (cmp102VerticalFDeriv F) := by
    unfold cmp102VerticalFDeriv
    fun_prop
  apply hasFDerivAt_intervalIntegral_of_continuous_fieldDerivative
      F (cmp102VerticalFDeriv F) hF.continuous hcont
  intro x t
  ·
    have hpath : HasFDerivAt (fun y : E => (y, t))
        (ContinuousLinearMap.inl ℝ E ℝ) x :=
      (hasFDerivAt_id (𝕜 := ℝ) (x := x)).prodMk
        (hasFDerivAt_const (x := x) t)
    exact
      ((hF.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp
        x hpath)

/-- If the vertical derivative of a jointly `C¹` integrand vanishes along
the zero-field interval, then its interval integral has zero derivative at
the origin. -/
theorem hasFDerivAt_intervalIntegral_zero_of_contDiff
    [FiniteDimensional ℝ E]
    (F : E × ℝ → ℝ) (hF : ContDiff ℝ 1 F)
    (hzero : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      cmp102VerticalFDeriv F (0, t) = 0) :
    HasFDerivAt
      (fun x : E => ∫ t in (0 : ℝ)..1, F (x, t))
      (0 : E →L[ℝ] ℝ) 0 := by
  have h :=
    hasFDerivAt_intervalIntegral_of_contDiff F hF
  have hintegral :
      (∫ t in (0 : ℝ)..1, cmp102VerticalFDeriv F (0, t)) =
        (0 : E →L[ℝ] ℝ) := by
    calc
      (∫ t in (0 : ℝ)..1, cmp102VerticalFDeriv F (0, t)) =
          ∫ _t in (0 : ℝ)..1, (0 : E →L[ℝ] ℝ) := by
            apply intervalIntegral.integral_congr
            intro t ht
            apply hzero t
            simpa [Set.uIcc_of_le zero_le_one] using ht
      _ = 0 := by simp
  simpa [hintegral] using h

end

end YangMills.RG
