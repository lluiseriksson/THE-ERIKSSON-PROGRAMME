/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalCoerciveCombesThomasInverse
import YangMills.RG.ShiftedCoerciveResolvent

/-!
# Uniform Combes--Thomas bounds for shifted coercive resolvents

For a finite-range coercive physical precision `K`, this module proves that
the entire shifted family `(K+tI)⁻¹`, `t ≥ 0`, has one common exponential
decay rate.  The amplitude improves with the shifted coercivity margin:

`|(K+tI)⁻¹(x,y)| ≤ 2/(c+t) exp(-θ d(x,y))`.

The extra scalar tilt condition controls the diagonal shift uniformly for
all `t`; no ambient-volume factor or `t`-dependent decay rate is introduced.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {d N Nc : ℕ} [NeZero N]

/-- A nonnegative scalar shift does not enlarge the physical kernel range. -/
theorem shiftedPrecisionCLM_finiteRange
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hself : ∀ p, dist p p = 0)
    {R : ℕ}
    (K : PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc)
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    (t : ℝ) :
    PhysicalCovarianceFiniteRange (shiftedPrecisionCLM K t) dist R := by
  intro source target v hfar
  have hne : target ≠ source := by
    intro h
    subst target
    rw [hself source] at hfar
    omega
  change
    K (singlePhysicalBondCochain source v) target +
      t • singlePhysicalBondCochain source v target = 0
  rw [hrange source target v hfar]
  simp [singlePhysicalBondCochain_of_ne (v := v) hne]

/-- The shifted precision has entrywise budget `M+t` for `t ≥ 0`. -/
theorem shiftedPrecisionCLM_kernelBound
    {M t : ℝ} (ht : 0 ≤ t)
    (K : PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc)
    (hbound :
      PhysicalCovarianceKernelBound K (fun _ _ => M)) :
    PhysicalCovarianceKernelBound
      (shiftedPrecisionCLM K t) (fun _ _ => M + t) := by
  intro source target v
  let δ :=
    singlePhysicalBondCochain
      (d := d) (N := N) (Nc := Nc) source v
  have hδpoint : ‖δ target‖ ≤ ‖v‖ := by
    calc
      ‖δ target‖ ≤ ‖δ‖ := PiLp.norm_apply_le δ target
      _ = ‖v‖ := norm_singlePhysicalBondCochain source v
  calc
    ‖shiftedPrecisionCLM K t δ target‖ =
        ‖K δ target + t • δ target‖ := by
      rfl
    _ ≤ ‖K δ target‖ + ‖t • δ target‖ := norm_add_le _ _
    _ ≤ M * ‖v‖ + t * ‖v‖ := by
      apply add_le_add
      · exact hbound source target v
      · rw [norm_smul, Real.norm_of_nonneg ht]
        exact mul_le_mul_of_nonneg_left hδpoint ht
    _ = (M + t) * ‖v‖ := by ring

/-- The two scalar tilt budgets combine uniformly under every nonnegative
shift. -/
theorem shifted_tiltBudget
    {M c a t n : ℝ}
    (ht : 0 ≤ t)
    (hbase : M * a * n ≤ c / 2)
    (hshift : a * n ≤ 1 / 2) :
    (M + t) * a * n ≤ (c + t) / 2 := by
  calc
    (M + t) * a * n =
        M * a * n + t * (a * n) := by ring
    _ ≤ c / 2 + t * (1 / 2) :=
      add_le_add hbase (mul_le_mul_of_nonneg_left hshift ht)
    _ = (c + t) / 2 := by ring

/-- Uniform-in-shift Combes--Thomas estimate for the physical shifted
resolvent. -/
theorem shiftedResolvent_exponentialKernelBound_of_coercive
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    (htri : ∀ p q s, dist p s ≤ dist p q + dist q s)
    (hself : ∀ p, dist p p = 0)
    {θ : ℝ} (hθ : 0 < θ)
    {R NR : ℕ} {M c t : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c) (ht : 0 ≤ t)
    (hNR : ∀ x : PhysicalBond d N,
      (Finset.univ.filter (fun y => dist x y ≤ R)).card ≤ NR)
    (K : PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc)
    (hrange : PhysicalCovarianceFiniteRange K dist R)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => M))
    (hcoer : IsCoerciveCLM K c)
    (hbaseBudget :
      M * (Real.exp (θ * (R : ℝ)) - 1) * (NR : ℝ) ≤ c / 2)
    (hshiftBudget :
      (Real.exp (θ * (R : ℝ)) - 1) * (NR : ℝ) ≤ 1 / 2) :
    PhysicalCovarianceExponentialKernelBound
      (shiftedResolventOfIsCoerciveCLM K hc hcoer t ht)
      dist (2 / (c + t)) θ := by
  apply physicalCovariance_exponentialKernelBound_of_coercive
    dist hsymm htri hself hθ
    (add_nonneg hM ht)
    (add_pos_of_pos_of_nonneg hc ht)
    hNR
  · exact shiftedPrecisionCLM_finiteRange dist hself K hrange t
  · exact shiftedPrecisionCLM_kernelBound ht K hbound
  · exact isCoerciveCLM_shiftedPrecisionCLM K hcoer
  · exact shiftedPrecision_comp_shiftedResolvent K hc hcoer t ht
  · exact shifted_tiltBudget ht hbaseBudget hshiftBudget

end

end YangMills.RG
