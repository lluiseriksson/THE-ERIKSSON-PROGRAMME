/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalInverseSqrtKernelDecay
import YangMills.RG.InverseSqrtResolventScalarIntegral

/-!
# Exponential localization of one physical canonical inverse square root

The root-difference module localizes `K₁⁻¹ᐟ² - K₀⁻¹ᐟ²`.  The first term in
the physical `R₃` telescope also needs the individual base root `K₀⁻¹ᐟ²`.
This module integrates the one-resolvent Balakrishnan kernel against the
uniform shifted Combes--Thomas estimate and evaluates the remaining scalar
integral exactly.  The terminal amplitude is `2 / sqrt c`, with no ambient
volume factor.
-/

namespace YangMills.RG

open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

variable {d N Nc : ℕ} [NeZero N]

/-- Integrating a one-resolvent Balakrishnan kernel preserves its exponential
decay rate. -/
theorem physicalCanonicalInverseSqrt_exponentialKernelBound_of_integrand
    {dBlock L lieDim : ℕ}
    [NeZero L]
    (D : PhysicalGaugeCMP116Dictionary d N Nc dBlock L lieDim)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    {Q κ c : ℝ}
    (hQ : 0 ≤ Q)
    (K : PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc)
    (hc : 0 < c)
    (hcoer : IsCoerciveCLM K c)
    (hK : (K : PhysicalGaugeOneCochain d N Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain d N Nc).IsSymmetric)
    (hκ : 0 < κ)
    (hKernel : ∀ t, 0 < t →
      PhysicalCovarianceExponentialKernelBound
        ((Real.sqrt t)⁻¹ •
          nonnegativeShiftedResolvent K hc hcoer t)
        dist
        (Q * inverseSqrtResolventScalarIntegrand c t)
        κ) :
    PhysicalCovarianceExponentialKernelBound
      (D.physicalCanonicalInverseSqrt K hc hcoer hK)
      dist
      (Real.pi⁻¹ * Q *
        (∫ t in Ioi 0, inverseSqrtResolventScalarIntegrand c t))
      κ := by
  have hscalarInt :
      Integrable
        (inverseSqrtResolventScalarIntegrand c)
        (volume.restrict (Ioi 0)) :=
    integrableOn_inverseSqrtResolventScalarIntegrand hc
  have hscalarNonneg :
      0 ≤ ∫ t in Ioi 0,
        inverseSqrtResolventScalarIntegrand c t := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro t ht
    change 0 < t at ht
    unfold inverseSqrtResolventScalarIntegrand
    positivity
  refine
    ⟨mul_nonneg
        (mul_nonneg (inv_pos.mpr Real.pi_pos).le hQ)
        hscalarNonneg,
      hκ, ?_⟩
  intro source target v
  let δ :=
    singlePhysicalBondCochain
      (d := d) (N := N) (Nc := Nc) source v
  let E := PhysicalGaugeOneCochain d N Nc
  let bondEval :
      E →L[ℝ] SUNLieCoord Nc :=
    (ContinuousLinearMap.proj target).comp
      (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : PhysicalBond d N => SUNLieCoord Nc)).toContinuousLinearMap
  let evalCLM :
      (E →L[ℝ] E) →L[ℝ] SUNLieCoord Nc :=
    bondEval.comp (ContinuousLinearMap.apply ℝ E δ)
  have heval (T : E →L[ℝ] E) :
      evalCLM T = T δ target := by
    rfl
  let F : ℝ → (E →L[ℝ] E) :=
    fun t =>
      (Real.sqrt t)⁻¹ •
        nonnegativeShiftedResolvent K hc hcoer t
  have hFmeas :
      AEStronglyMeasurable F (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply ContinuousOn.smul
    · apply ContinuousOn.inv₀
      · exact Real.continuous_sqrt.continuousOn
      · intro t ht
        exact (Real.sqrt_pos.2 ht).ne'
    · exact continuousOn_nonnegativeShiftedResolvent K hc hcoer
  have hFint :
      Integrable F (volume.restrict (Ioi 0)) := by
    refine Integrable.mono' hscalarInt hFmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    rw [show F t =
        (Real.sqrt t)⁻¹ •
          shiftedResolventOfIsCoerciveCLM K hc hcoer t ht.le by
      dsimp [F]
      rw [nonnegativeShiftedResolvent_eq_of_nonneg
        K hc hcoer t ht.le]]
    rw [norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg t))]
    unfold inverseSqrtResolventScalarIntegrand
    exact mul_le_mul_of_nonneg_left
      (norm_shiftedResolventOfIsCoerciveCLM_le
        K hc hcoer t ht.le)
      (inv_nonneg.mpr (Real.sqrt_nonneg t))
  have hEvalIntegral :
      evalCLM (∫ t in Ioi 0, F t) =
        ∫ t in Ioi 0, evalCLM (F t) :=
    (evalCLM.integral_comp_comm hFint).symm
  let spatial :=
    Real.exp (-(κ * (dist target source : ℝ))) * ‖v‖
  have hspatial : 0 ≤ spatial := by
    dsimp [spatial]
    positivity
  have hmajorant :
      Integrable
        (fun t => (Q * spatial) *
          inverseSqrtResolventScalarIntegrand c t)
        (volume.restrict (Ioi 0)) :=
    hscalarInt.const_mul (Q * spatial)
  have hEvalBound :
      ‖∫ t in Ioi 0, evalCLM (F t)‖ ≤
        ∫ t in Ioi 0,
          (Q * spatial) *
            inverseSqrtResolventScalarIntegrand c t := by
    apply norm_integral_le_of_norm_le hmajorant
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    have hpoint := (hKernel t ht).2.2 source target v
    rw [heval]
    calc
      ‖F t δ target‖ ≤
          (Q * inverseSqrtResolventScalarIntegrand c t) *
            Real.exp (-(κ * (dist target source : ℝ))) * ‖v‖ :=
        hpoint
      _ = (Q * spatial) *
          inverseSqrtResolventScalarIntegrand c t := by
        dsimp [spatial]
        ring
  rw [
    PhysicalGaugeCMP116Dictionary.physicalCanonicalInverseSqrt_eq_inv_pi_smul_integral_kernel
      D K hc hcoer hK]
  change
    ‖Real.pi⁻¹ • evalCLM (∫ t in Ioi 0, F t)‖ ≤
      (Real.pi⁻¹ * Q *
        (∫ t in Ioi 0, inverseSqrtResolventScalarIntegrand c t)) *
        Real.exp (-(κ * (dist target source : ℝ))) * ‖v‖
  rw [hEvalIntegral, norm_smul,
    Real.norm_of_nonneg (inv_pos.mpr Real.pi_pos).le]
  calc
    Real.pi⁻¹ * ‖∫ t in Ioi 0, evalCLM (F t)‖
        ≤ Real.pi⁻¹ *
            (∫ t in Ioi 0,
              (Q * spatial) *
                inverseSqrtResolventScalarIntegrand c t) :=
      mul_le_mul_of_nonneg_left hEvalBound
        (inv_pos.mpr Real.pi_pos).le
    _ = Real.pi⁻¹ *
          ((Q * spatial) *
            (∫ t in Ioi 0,
              inverseSqrtResolventScalarIntegrand c t)) := by
      rw [integral_const_mul]
    _ = (Real.pi⁻¹ * Q *
          (∫ t in Ioi 0,
            inverseSqrtResolventScalarIntegrand c t)) *
          Real.exp (-(κ * (dist target source : ℝ))) * ‖v‖ := by
      dsimp [spatial]
      ring

/-- End-to-end one-root localization.  Shifted Combes--Thomas and the exact
scalar Balakrishnan integral are discharged internally. -/
theorem physicalCanonicalInverseSqrt_exponentialKernelBound_of_coercive
    {dBlock L lieDim : ℕ}
    [NeZero L]
    (D : PhysicalGaugeCMP116Dictionary d N Nc dBlock L lieDim)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (htri : ∀ p q s, dist p s ≤ dist p q + dist q s)
    (hself : ∀ p, dist p p = 0)
    {θ : ℝ} (hθ : 0 < θ)
    {R NR : ℕ} {M c : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c)
    (hNR : ∀ x : PhysicalBond d N,
      (Finset.univ.filter (fun y => dist x y ≤ R)).card ≤ NR)
    (K : PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc)
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => M))
    (hcoer : IsCoerciveCLM K c)
    (hK : (K : PhysicalGaugeOneCochain d N Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain d N Nc).IsSymmetric)
    (hbaseBudget :
      M * (Real.exp (θ * (R : ℝ)) - 1) * (NR : ℝ) ≤ c / 2)
    (hshiftBudget :
      (Real.exp (θ * (R : ℝ)) - 1) * (NR : ℝ) ≤ 1 / 2) :
    PhysicalCovarianceExponentialKernelBound
      (D.physicalCanonicalInverseSqrt K hc hcoer hK)
      dist (2 * (Real.sqrt c)⁻¹) θ := by
  have hroot :=
    physicalCanonicalInverseSqrt_exponentialKernelBound_of_integrand
      D dist (Q := 2) (by norm_num)
      K hc hcoer hK hθ
      (fun t ht => by
        rw [nonnegativeShiftedResolvent_eq_of_nonneg
          K hc hcoer t ht.le]
        have hres :=
          shiftedResolvent_exponentialKernelBound_of_coercive
            dist hsymm htri hself hθ hM hc ht.le hNR
            K hrange hbound hcoer hbaseBudget hshiftBudget
        have hscaled :=
          physicalCovarianceExponentialKernelBound_smul
            dist (inv_nonneg.mpr (Real.sqrt_nonneg t))
            (shiftedResolventOfIsCoerciveCLM K hc hcoer t ht.le)
            hres
        convert hscaled using 1 <;>
          simp only [inverseSqrtResolventScalarIntegrand,
            div_eq_mul_inv] <;>
          ring)
  rw [integral_inverseSqrtResolventScalarIntegrand hc] at hroot
  convert hroot using 1
  field_simp [Real.pi_ne_zero]

end

end YangMills.RG
