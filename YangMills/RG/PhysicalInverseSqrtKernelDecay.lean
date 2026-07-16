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

end

end YangMills.RG
