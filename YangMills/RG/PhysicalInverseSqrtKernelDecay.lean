/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalExponentialKernelComposition
import YangMills.RG.PhysicalInverseSqrtBalakrishnan
import YangMills.RG.PhysicalShiftedCombesThomas

/-!
# Exponential localization of the inverse-root difference kernel

The exact Balakrishnan integrand has the noncommutative factorization

`t⁻¹ᐟ² (K₁+tI)⁻¹ (K₀-K₁) (K₀+tI)⁻¹`.

This module combines the uniform shifted Combes--Thomas estimates with the
physical block-kernel convolution theorem.  The result is a pointwise
exponential kernel bound for the full factorized integrand, uniform in the
ambient volume.  Integrating this estimate to obtain the final root-difference
kernel bound is the next checkpoint.
-/

namespace YangMills.RG

open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

variable {d N Nc : ℕ} [NeZero N]

/-- Exponential localization of the factorized inverse-root integrand from
localized bounds on its three factors. -/
theorem inverseSqrtResolventDifferenceKernel_exponentialKernelBound
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (htri : ∀ x y z, dist x y ≤ dist x z + dist z y)
    {A₀ A₂ A₁ κ σ S c₀ c₁ t : ℝ}
    (hσ : 0 ≤ σ)
    (h2σκ : 2 * σ < κ)
    (hS : 0 ≤ S)
    (K₀ K₁ : PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hK₀ : IsCoerciveCLM K₀ c₀)
    (hK₁ : IsCoerciveCLM K₁ c₁)
    (ht : 0 ≤ t)
    (hRes₀ : PhysicalCovarianceExponentialKernelBound
      (shiftedResolventOfIsCoerciveCLM K₀ hc₀ hK₀ t ht)
      dist A₀ κ)
    (hR₂ : PhysicalCovarianceExponentialKernelBound
      (K₀ - K₁) dist A₂ κ)
    (hRes₁ : PhysicalCovarianceExponentialKernelBound
      (shiftedResolventOfIsCoerciveCLM K₁ hc₁ hK₁ t ht)
      dist A₁ κ)
    (hsum : ∀ x,
      ∑ z : PhysicalBond d N,
        Real.exp (-(σ * (dist x z : ℝ))) ≤ S) :
    PhysicalCovarianceExponentialKernelBound
      (inverseSqrtResolventDifferenceKernel
        K₀ K₁ hc₀ hc₁ hK₀ hK₁ t)
      dist
      ((Real.sqrt t)⁻¹ * (A₁ * (A₂ * A₀ * S) * S))
      ((κ - σ) - σ) := by
  rw [inverseSqrtResolventDifferenceKernel_eq_factorized
    K₀ K₁ hc₀ hc₁ hK₀ hK₁ t ht]
  apply physicalCovarianceExponentialKernelBound_smul
    dist (inv_nonneg.mpr (Real.sqrt_nonneg t))
  exact physicalCovarianceExponentialKernelBound_comp_three
    dist htri hσ h2σκ hS
    (shiftedResolventOfIsCoerciveCLM K₁ hc₁ hK₁ t ht)
    (K₀ - K₁)
    (shiftedResolventOfIsCoerciveCLM K₀ hc₀ hK₀ t ht)
    hRes₁ hR₂ hRes₀ hsum

/-- Fully shifted-Combes--Thomas-fed localization of the Balakrishnan
integrand.  The caller supplies only the physical finite-range/coercivity
certificates for the two precisions, the already-proved localization of `R₂`,
and the geometric exponential-sum bound. -/
theorem inverseSqrtResolventDifferenceKernel_exponentialKernelBound_of_coercive
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (htri : ∀ p q s, dist p s ≤ dist p q + dist q s)
    (hself : ∀ p, dist p p = 0)
    {θ σ : ℝ} (hθ : 0 < θ)
    (hσ : 0 ≤ σ)
    (h2σθ : 2 * σ < θ)
    {R NR : ℕ} {M₀ M₁ c₀ c₁ A₂ S t : ℝ}
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (ht : 0 ≤ t) (hS : 0 ≤ S)
    (hNR : ∀ x : PhysicalBond d N,
      (Finset.univ.filter (fun y => dist x y ≤ R)).card ≤ NR)
    (K₀ K₁ : PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc)
    (hrange₀ : PhysicalCovarianceFiniteRange K₀ dist R)
    (hrange₁ : PhysicalCovarianceFiniteRange K₁ dist R)
    (hbound₀ : PhysicalCovarianceKernelBound K₀ (fun _ _ => M₀))
    (hbound₁ : PhysicalCovarianceKernelBound K₁ (fun _ _ => M₁))
    (hcoer₀ : IsCoerciveCLM K₀ c₀)
    (hcoer₁ : IsCoerciveCLM K₁ c₁)
    (hbaseBudget₀ :
      M₀ * (Real.exp (θ * (R : ℝ)) - 1) * (NR : ℝ) ≤ c₀ / 2)
    (hbaseBudget₁ :
      M₁ * (Real.exp (θ * (R : ℝ)) - 1) * (NR : ℝ) ≤ c₁ / 2)
    (hshiftBudget :
      (Real.exp (θ * (R : ℝ)) - 1) * (NR : ℝ) ≤ 1 / 2)
    (hR₂ : PhysicalCovarianceExponentialKernelBound
      (K₀ - K₁) dist A₂ θ)
    (hsum : ∀ x,
      ∑ z : PhysicalBond d N,
        Real.exp (-(σ * (dist x z : ℝ))) ≤ S) :
    PhysicalCovarianceExponentialKernelBound
      (inverseSqrtResolventDifferenceKernel
        K₀ K₁ hc₀ hc₁ hcoer₀ hcoer₁ t)
      dist
      ((Real.sqrt t)⁻¹ *
        ((2 / (c₁ + t)) * (A₂ * (2 / (c₀ + t)) * S) * S))
      ((θ - σ) - σ) := by
  apply inverseSqrtResolventDifferenceKernel_exponentialKernelBound
    dist (fun x y z => htri x z y) hσ h2σθ hS
    K₀ K₁ hc₀ hc₁ hcoer₀ hcoer₁ ht
  · exact shiftedResolvent_exponentialKernelBound_of_coercive
      dist hsymm htri hself hθ hM₀ hc₀ ht hNR
      K₀ hrange₀ hbound₀ hcoer₀ hbaseBudget₀ hshiftBudget
  · exact hR₂
  · exact shiftedResolvent_exponentialKernelBound_of_coercive
      dist hsymm htri hself hθ hM₁ hc₁ ht hNR
      K₁ hrange₁ hbound₁ hcoer₁ hbaseBudget₁ hshiftBudget
  · exact hsum

/-- Integrating an exponentially localized Balakrishnan integrand preserves
its decay rate.  The proof evaluates the Bochner integral on a single-bond
probe and at one target bond, so it does not pass through the global operator
norm and introduces no volume factor. -/
theorem physicalCanonicalInverseSqrt_sub_exponentialKernelBound_of_integrand
    {dBlock L lieDim : ℕ}
    [NeZero L]
    (D : PhysicalGaugeCMP116Dictionary d N Nc dBlock L lieDim)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    {Q κ c₀ c₁ : ℝ}
    (hQ : 0 ≤ Q)
    (K₀ K₁ : PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hcoer₀ : IsCoerciveCLM K₀ c₀)
    (hcoer₁ : IsCoerciveCLM K₁ c₁)
    (hK₀ : (K₀ : PhysicalGaugeOneCochain d N Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain d N Nc).IsSymmetric)
    (hK₁ : (K₁ : PhysicalGaugeOneCochain d N Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain d N Nc).IsSymmetric)
    (hκ : 0 < κ)
    (hKernel : ∀ t, 0 < t →
      PhysicalCovarianceExponentialKernelBound
        (inverseSqrtResolventDifferenceKernel
          K₀ K₁ hc₀ hc₁ hcoer₀ hcoer₁ t)
        dist (Q * inverseSqrtTwoMarginScalar c₀ c₁ t) κ) :
    PhysicalCovarianceExponentialKernelBound
      (D.physicalCanonicalInverseSqrt K₁ hc₁ hcoer₁ hK₁ -
        D.physicalCanonicalInverseSqrt K₀ hc₀ hcoer₀ hK₀)
      dist
      (Real.pi⁻¹ * Q *
        (∫ t in Ioi 0, inverseSqrtTwoMarginScalar c₀ c₁ t))
      κ := by
  have hscalarInt :
      Integrable
        (inverseSqrtTwoMarginScalar c₀ c₁)
        (volume.restrict (Ioi 0)) :=
    integrableOn_inverseSqrtTwoMarginScalar hc₀ hc₁
  have hscalarNonneg :
      0 ≤ ∫ t in Ioi 0, inverseSqrtTwoMarginScalar c₀ c₁ t := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro t ht
    change 0 < t at ht
    unfold inverseSqrtTwoMarginScalar
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
    inverseSqrtResolventDifferenceKernel
      K₀ K₁ hc₀ hc₁ hcoer₀ hcoer₁
  have hFint :
      Integrable F (volume.restrict (Ioi 0)) :=
    integrableOn_inverseSqrtResolventDifferenceKernel
      K₀ K₁ hc₀ hc₁ hcoer₀ hcoer₁
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
          inverseSqrtTwoMarginScalar c₀ c₁ t)
        (volume.restrict (Ioi 0)) :=
    hscalarInt.const_mul (Q * spatial)
  have hEvalBound :
      ‖∫ t in Ioi 0, evalCLM (F t)‖ ≤
        ∫ t in Ioi 0,
          (Q * spatial) * inverseSqrtTwoMarginScalar c₀ c₁ t := by
    apply norm_integral_le_of_norm_le hmajorant
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    have hpoint := (hKernel t ht).2.2 source target v
    rw [heval]
    calc
      ‖F t δ target‖ ≤
          (Q * inverseSqrtTwoMarginScalar c₀ c₁ t) *
            Real.exp (-(κ * (dist target source : ℝ))) * ‖v‖ :=
        hpoint
      _ = (Q * spatial) *
          inverseSqrtTwoMarginScalar c₀ c₁ t := by
        dsimp [spatial]
        ring
  rw [
    PhysicalGaugeCMP116Dictionary.physicalCanonicalInverseSqrt_sub_eq_inv_pi_smul_integral_kernel
      D K₀ K₁ hc₀ hc₁ hcoer₀ hcoer₁ hK₀ hK₁]
  change
    ‖Real.pi⁻¹ • evalCLM (∫ t in Ioi 0, F t)‖ ≤
      (Real.pi⁻¹ * Q *
        (∫ t in Ioi 0, inverseSqrtTwoMarginScalar c₀ c₁ t)) *
        Real.exp (-(κ * (dist target source : ℝ))) * ‖v‖
  rw [hEvalIntegral, norm_smul,
    Real.norm_of_nonneg (inv_pos.mpr Real.pi_pos).le]
  calc
    Real.pi⁻¹ * ‖∫ t in Ioi 0, evalCLM (F t)‖
        ≤ Real.pi⁻¹ *
            (∫ t in Ioi 0,
              (Q * spatial) * inverseSqrtTwoMarginScalar c₀ c₁ t) :=
      mul_le_mul_of_nonneg_left hEvalBound
        (inv_pos.mpr Real.pi_pos).le
    _ = Real.pi⁻¹ *
          ((Q * spatial) *
            (∫ t in Ioi 0, inverseSqrtTwoMarginScalar c₀ c₁ t)) := by
      rw [integral_const_mul]
    _ = (Real.pi⁻¹ * Q *
          (∫ t in Ioi 0, inverseSqrtTwoMarginScalar c₀ c₁ t)) *
          Real.exp (-(κ * (dist target source : ℝ))) * ‖v‖ := by
      dsimp [spatial]
      ring

/-- End-to-end real-sector exponential localization of the physical canonical
inverse-root difference.  Shifted Combes--Thomas, two physical block
convolutions, and the Bochner integration are all discharged internally. -/
theorem physicalCanonicalInverseSqrt_sub_exponentialKernelBound_of_coercive
    {dBlock L lieDim : ℕ}
    [NeZero L]
    (D : PhysicalGaugeCMP116Dictionary d N Nc dBlock L lieDim)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (htri : ∀ p q s, dist p s ≤ dist p q + dist q s)
    (hself : ∀ p, dist p p = 0)
    {θ σ : ℝ} (hθ : 0 < θ)
    (hσ : 0 ≤ σ)
    (h2σθ : 2 * σ < θ)
    {R NR : ℕ} {M₀ M₁ c₀ c₁ A₂ S : ℝ}
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hS : 0 ≤ S)
    (hNR : ∀ x : PhysicalBond d N,
      (Finset.univ.filter (fun y => dist x y ≤ R)).card ≤ NR)
    (K₀ K₁ : PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc)
    (hrange₀ : PhysicalCovarianceFiniteRange K₀ dist R)
    (hrange₁ : PhysicalCovarianceFiniteRange K₁ dist R)
    (hbound₀ : PhysicalCovarianceKernelBound K₀ (fun _ _ => M₀))
    (hbound₁ : PhysicalCovarianceKernelBound K₁ (fun _ _ => M₁))
    (hcoer₀ : IsCoerciveCLM K₀ c₀)
    (hcoer₁ : IsCoerciveCLM K₁ c₁)
    (hK₀ : (K₀ : PhysicalGaugeOneCochain d N Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain d N Nc).IsSymmetric)
    (hK₁ : (K₁ : PhysicalGaugeOneCochain d N Nc →ₗ[ℝ]
      PhysicalGaugeOneCochain d N Nc).IsSymmetric)
    (hbaseBudget₀ :
      M₀ * (Real.exp (θ * (R : ℝ)) - 1) * (NR : ℝ) ≤ c₀ / 2)
    (hbaseBudget₁ :
      M₁ * (Real.exp (θ * (R : ℝ)) - 1) * (NR : ℝ) ≤ c₁ / 2)
    (hshiftBudget :
      (Real.exp (θ * (R : ℝ)) - 1) * (NR : ℝ) ≤ 1 / 2)
    (hR₂ : PhysicalCovarianceExponentialKernelBound
      (K₀ - K₁) dist A₂ θ)
    (hsum : ∀ x,
      ∑ z : PhysicalBond d N,
        Real.exp (-(σ * (dist x z : ℝ))) ≤ S) :
    PhysicalCovarianceExponentialKernelBound
      (D.physicalCanonicalInverseSqrt K₁ hc₁ hcoer₁ hK₁ -
        D.physicalCanonicalInverseSqrt K₀ hc₀ hcoer₀ hK₀)
      dist
      (Real.pi⁻¹ * (4 * A₂ * S * S) *
        (∫ t in Ioi 0, inverseSqrtTwoMarginScalar c₀ c₁ t))
      ((θ - σ) - σ) := by
  apply physicalCanonicalInverseSqrt_sub_exponentialKernelBound_of_integrand
    D dist
    (Q := 4 * A₂ * S * S)
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) hR₂.1) hS) hS)
    K₀ K₁ hc₀ hc₁ hcoer₀ hcoer₁ hK₀ hK₁
    (by linarith)
  intro t ht
  have hlocal :=
    inverseSqrtResolventDifferenceKernel_exponentialKernelBound_of_coercive
      dist hsymm htri hself hθ hσ h2σθ
      hM₀ hM₁ hc₀ hc₁ ht.le hS hNR
      K₀ K₁ hrange₀ hrange₁ hbound₀ hbound₁
      hcoer₀ hcoer₁ hbaseBudget₀ hbaseBudget₁ hshiftBudget
      hR₂ hsum
  convert hlocal using 1 <;>
    simp only [inverseSqrtTwoMarginScalar, div_eq_mul_inv] <;>
    ring

end

end YangMills.RG
