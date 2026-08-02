/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import YangMills.RG.PhysicalGaugeCovarianceLocalization

/-!
# Scalar Stieltjes integral

This module begins the analytic layer needed to turn the shift-uniform
resolvent estimate into localization of the positive covariance root.
-/

namespace YangMills.RG

open MeasureTheory Set Filter

private noncomputable def stieltjesPrimitive (c : ℝ) : ℝ → ℝ :=
  fun t => (Real.sqrt c)⁻¹ * Real.arctan (t / Real.sqrt c)

private theorem hasDerivAt_stieltjesPrimitive {c t : ℝ} (hc : 0 < c) :
    HasDerivAt (stieltjesPrimitive c) ((c + t ^ 2)⁻¹) t := by
  let a := Real.sqrt c
  have ha : 0 < a := Real.sqrt_pos.2 hc
  have ha2 : a ^ 2 = c := Real.sq_sqrt hc.le
  convert ((Real.hasDerivAt_arctan (t / a)).const_mul a⁻¹).comp t
    ((hasDerivAt_id t).div_const a) using 1
  all_goals field_simp
  all_goals nlinarith

private theorem tendsto_stieltjesPrimitive_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (stieltjesPrimitive c) atTop
      (nhds ((Real.sqrt c)⁻¹ * (Real.pi / 2))) := by
  let a := Real.sqrt c
  have ha : 0 < a := Real.sqrt_pos.2 hc
  have hA : Tendsto (fun t : ℝ => Real.arctan (t / a)) atTop
      (nhds (Real.pi / 2)) := by
    simpa [Function.comp_def] using
      ((tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
        (tendsto_id.atTop_div_const ha))
  exact hA.const_mul a⁻¹

/-- The scalar Stieltjes integrand is Bochner integrable on the positive
half-line. -/
theorem integrableOn_Ioi_inv_add_sq {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => (c + t ^ 2)⁻¹) (Ioi 0) := by
  apply integrableOn_Ioi_deriv_of_nonneg'
    (g := stieltjesPrimitive c)
    (l := (Real.sqrt c)⁻¹ * (Real.pi / 2))
  · intro t _
    exact hasDerivAt_stieltjesPrimitive hc
  · intro t _
    positivity
  · exact tendsto_stieltjesPrimitive_atTop hc

/-- The scalar integral occurring in the inverse-square-root Stieltjes
formula. -/
theorem integral_Ioi_inv_add_sq {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi 0, (c + t ^ 2)⁻¹) = Real.pi / (2 * Real.sqrt c) := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t _ => hasDerivAt_stieltjesPrimitive hc)
    (integrableOn_Ioi_inv_add_sq hc)
    (tendsto_stieltjesPrimitive_atTop hc)]
  dsimp [stieltjesPrimitive]
  rw [zero_div, Real.arctan_zero, mul_zero, sub_zero]
  field_simp

/-- The normalized Bochner integral used in the inverse-square-root
Stieltjes formula. -/
noncomputable def stieltjesIntegralOperator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E →L[ℝ] E) : E →L[ℝ] E :=
  (2 / Real.pi) • ∫ t : ℝ in Ioi 0, F t

/-- Integrating a resolvent kernel estimate of shape
`A / (c + t²) * weight` gives the exact Stieltjes constant
`A / √c * weight`.  This theorem is independent of the still-open
identification of the spectral root with the resolvent integral. -/
theorem physicalCovarianceKernelBound_stieltjesIntegralOperator
    {d N Nc : ℕ} [NeZero N]
    {c A : ℝ} (hc : 0 < c)
    (weight : PhysicalBond d N → PhysicalBond d N → ℝ)
    (F : ℝ →
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc)
    (hFint : IntegrableOn F (Ioi 0))
    (hkernel : ∀ t ∈ Ioi (0 : ℝ),
      PhysicalCovarianceKernelBound (F t)
        (fun target source => A / (c + t ^ 2) * weight target source)) :
    PhysicalCovarianceKernelBound (stieltjesIntegralOperator F)
      (fun target source => A / Real.sqrt c * weight target source) := by
  intro source target v
  let δ := singlePhysicalBondCochain
    (d := d) (N := N) (Nc := Nc) source v
  let w := weight target source
  let g : ℝ → ℝ := fun t => (A * w * ‖v‖) * (c + t ^ 2)⁻¹
  have hFapp : IntegrableOn (fun t => F t δ) (Ioi 0) :=
    (ContinuousLinearMap.apply ℝ
      (PhysicalGaugeOneCochain d N Nc) δ).integrable_comp hFint
  have hcoord :
      ((∫ t : ℝ in Ioi 0, F t δ) target) =
        ∫ t : ℝ in Ioi 0, (F t δ) target := by
    change (PiLp.proj (𝕜 := ℝ) 2
        (fun _ : PhysicalBond d N => SUNLieCoord Nc) target)
        (∫ t : ℝ in Ioi 0, F t δ) = _
    exact ((PiLp.proj (𝕜 := ℝ) 2
      (fun _ : PhysicalBond d N => SUNLieCoord Nc) target).integral_comp_comm hFapp).symm
  have hg : IntegrableOn g (Ioi 0) := by
    simpa [g, mul_assoc] using
      (integrableOn_Ioi_inv_add_sq hc).const_mul (A * w * ‖v‖)
  have hmajor : ∀ᵐ t ∂volume.restrict (Ioi 0),
      ‖(F t δ) target‖ ≤ g t := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro t ht
    have htbound := hkernel t ht source target v
    simpa [δ, g, w, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htbound
  have hnorm :
      ‖(∫ t : ℝ in Ioi 0, (F t δ) target)‖ ≤
        ∫ t : ℝ in Ioi 0, g t :=
    norm_integral_le_of_norm_le hg hmajor
  have hgint :
      (∫ t : ℝ in Ioi 0, g t) =
        (A * w * ‖v‖) * (Real.pi / (2 * Real.sqrt c)) := by
    simp only [g, integral_const_mul]
    rw [integral_Ioi_inv_add_sq hc]
  unfold stieltjesIntegralOperator
  change ‖((2 / Real.pi) • ((∫ t : ℝ in Ioi 0, F t) δ)) target‖ ≤
    A / Real.sqrt c * weight target source * ‖v‖
  rw [PiLp.smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos (by positivity) Real.pi_pos),
    ContinuousLinearMap.integral_apply hFint δ, hcoord]
  calc
    2 / Real.pi * ‖∫ t : ℝ in Ioi 0, (F t δ) target‖
        ≤ 2 / Real.pi * (∫ t : ℝ in Ioi 0, g t) := by
          exact mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = A / Real.sqrt c * weight target source * ‖v‖ := by
      rw [hgint]
      dsimp [w]
      field_simp [Real.pi_ne_zero, (Real.sqrt_pos.2 hc).ne']

/-- Exponential form of the integrated kernel theorem. -/
theorem physicalCovariance_exponentialKernelBound_stieltjesIntegralOperator
    {d N Nc : ℕ} [NeZero N]
    {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (F : ℝ →
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc)
    (hFint : IntegrableOn F (Ioi 0))
    (hkernel : ∀ t ∈ Ioi (0 : ℝ),
      PhysicalCovarianceExponentialKernelBound (F t) dist
        (2 / (c + t ^ 2)) θ) :
    PhysicalCovarianceExponentialKernelBound
      (stieltjesIntegralOperator F) dist (2 / Real.sqrt c) θ := by
  refine ⟨by positivity, hθ, ?_⟩
  exact physicalCovarianceKernelBound_stieltjesIntegralOperator hc
    (fun target source =>
      Real.exp (- (θ * (dist target source : ℝ)))) F hFint
    (fun t ht => hkernel t ht |>.2.2)

end YangMills.RG
