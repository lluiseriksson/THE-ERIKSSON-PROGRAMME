/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib
import YangMills.RG.PhysicalShellLocalityQ
import YangMills.RG.PhysicalCoerciveCombesThomasInverse

/-!
# `CT_fixedVolume` — the Combes–Thomas endpoint on the flat physical shell
(`hRpoly` campaign — P4-CT ladder, owner acceptance criterion, plan §3ter)

This is the LITERAL endpoint of the P4-CT acceptance list: for the actual
fixed-volume flat physical covariance `flatGaugeFixedCovarianceCLM` at the
named free shell (`zeroSigma`, the `Empty` perturbation family),

`PhysicalCovarianceExponentialKernelBound
  (flatGaugeFixedCovarianceCLM …) physicalBondDist (2/c) θ`

with `c = min 1 a / CP` the fixed-volume block-Poincaré coercivity constant.
Every ingredient is the PROVED one — no substitute operator anywhere:

* the operator is the inverse of `flatGaugeFixedPrecisionCLM` at
  `Sigma := (Empty.elim)`, which IS the base precision `K₀ + a·Q†Q`
  (`flatGaugeFixedPrecisionCLM_zeroSigma_eq_base`, Addendum 474);
* locality of that base precision is the proved stencil package: range `3L`
  and entry bound `(4d)² + 4 + |a|L²` in the concrete `physicalBondDist`
  (Addenda 472–474);
* the ball constant is the proved `N_R = (2(3L+1))^d·d`
  (`physicalBondDist_ball_card_le`, Addendum 470);
* coercivity is the fixed-volume flat Hodge/block-Poincaré theorem
  (`flatGaugeFixedPrecision_coerciveWithPositiveConstant_of_flatPoincare`);
* the kernel extraction is CT4 at `r := source`
  (`physicalCovariance_exponentialKernelBound_of_coercive`, this ladder);
* the `0 < θ` witness is explicit
  (`exists_pos_tiltBudget`): the existence corollary produces a POSITIVE
  rate from the physical constants alone.

**Honest scope.**  Fixed volume: `CP` (hence `c` and `θ`) may depend on
`(d, L, N')` — the volume-uniform Poincaré constant remains a separate open
item (§3ter guard).  This discharges the `hkernel` SHAPE consumed by
`PhysicalLocalizedCovarianceCertificate` for the flat shell; it does not
identify the shell with a Wilson Hessian, localize the covariance ROOT,
prove `hRpoly`, the mass gap, or Clay.

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

variable {d L N' Nc : ℕ}
  [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc] [NeZero (L * N')]

/-- The empty (`zeroSigma`) perturbation weight family is summable. -/
theorem zeroSigma_delta_summable :
    Summable (fun i : Empty => (i.elim : ℝ)) :=
  summable_empty

/-- The empty (`zeroSigma`) perturbation family satisfies its weight bound
vacuously. -/
theorem zeroSigma_norm_le :
    ∀ i : Empty,
      ‖(i.elim :
          FinePhysicalOneCochain d L N' Nc →L[ℝ]
            FinePhysicalOneCochain d L N' Nc)‖ ≤ (i.elim : ℝ) :=
  fun i => i.elim

/-- The empty (`zeroSigma`) perturbation budget is strict for any positive
`a` and any fixed-volume Poincaré constant. -/
theorem zeroSigma_budget
    (ρ : SUNAdjointModel Nc) {a CP : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc ρ CP) :
    (∑' i : Empty, (i.elim : ℝ)) < min 1 a / CP := by
  rw [tsum_empty]
  exact div_pos (lt_min one_pos ha) hP.1

/-- **`CT_fixedVolume`** — the owner-acceptance endpoint: the fixed-volume
flat physical covariance at the `zeroSigma` free shell satisfies the
source-facing exponential kernel bound
`‖(C δ_p v) q‖ ≤ (2/c)·e^{−θ·physicalBondDist q p}·‖v‖` with
`c = min 1 a / CP`, for every positive tilt rate `θ` meeting the explicit
θ-budget at the proved shell constants (`M = (4d)² + 4 + |a|L²`, `R = 3L`,
`N_R = (2(3L+1))^d·d`). -/
theorem flatGaugeFixedCovariance_CT_fixedVolume
    (ρ : SUNAdjointModel Nc) {a CP : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc ρ CP)
    {θ : ℝ} (hθ : 0 < θ)
    (hbudget :
      ((((4 * d : ℕ) : ℝ) ^ 2 + (2 : ℝ) ^ 2) + |a| * (L : ℝ) ^ 2) *
          (Real.exp (θ * ((3 * L : ℕ) : ℝ)) - 1) *
          (((2 * (3 * L + 1)) ^ d * d : ℕ) : ℝ)
        ≤ min 1 a / CP / 2) :
    PhysicalCovarianceExponentialKernelBound
      (flatGaugeFixedCovarianceCLM ρ (fun i : Empty => i.elim)
        (fun i : Empty => i.elim) ha hP zeroSigma_delta_summable
        zeroSigma_norm_le (zeroSigma_budget ρ ha hP))
      physicalBondDist (2 / (min 1 a / CP)) θ := by
  -- coercivity of the shell at the fixed-volume Poincaré constant
  obtain ⟨-, hcoer⟩ :=
    flatGaugeFixedPrecision_coerciveWithPositiveConstant_of_flatPoincare
      ρ (fun i : Empty => i.elim) (fun i : Empty => i.elim) ha hP
      zeroSigma_delta_summable zeroSigma_norm_le (zeroSigma_budget ρ ha hP)
  rw [tsum_empty, sub_zero] at hcoer
  -- proved locality of the base precision, transported to the zeroSigma shell
  have hrange : PhysicalCovarianceFiniteRange
      (flatGaugeFixedPrecisionCLM d L N' Nc ρ a (fun i : Empty => i.elim))
      physicalBondDist (3 * L) := by
    rw [flatGaugeFixedPrecisionCLM_zeroSigma_eq_base]
    exact flatBasePrecision_finiteRange ρ a
  have hbound : PhysicalCovarianceKernelBound
      (flatGaugeFixedPrecisionCLM d L N' Nc ρ a (fun i : Empty => i.elim))
      (fun _ _ =>
        (((4 * d : ℕ) : ℝ) ^ 2 + (2 : ℝ) ^ 2) + |a| * (L : ℝ) ^ 2) := by
    rw [flatGaugeFixedPrecisionCLM_zeroSigma_eq_base]
    exact flatBasePrecision_kernelBound ρ a
  -- CT4 at the shell constants
  exact physicalCovariance_exponentialKernelBound_of_coercive
    physicalBondDist physicalBondDist_comm physicalBondDist_triangle
    physicalBondDist_self hθ
    (by positivity)
    (div_pos (lt_min one_pos ha) hP.1)
    (fun x => physicalBondDist_ball_card_le x (3 * L))
    hrange hbound hcoer
    (precision_comp_flatGaugeFixedCovarianceCLM
      ρ (fun i : Empty => i.elim) (fun i : Empty => i.elim) ha hP
      zeroSigma_delta_summable zeroSigma_norm_le (zeroSigma_budget ρ ha hP))
    hbudget

/-- **`CT_fixedVolume`, positive-rate form** — the `0 < θ` witness at the
physical constants: some explicit positive tilt rate satisfies the budget,
so the flat shell covariance is exponentially localized with A PROVED
POSITIVE rate.  Fixed volume; the rate may depend on `(d, L, N', a, CP)`. -/
theorem exists_flatGaugeFixedCovariance_CT_fixedVolume
    (ρ : SUNAdjointModel Nc) {a CP : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc ρ CP) :
    ∃ θ : ℝ, 0 < θ ∧
      PhysicalCovarianceExponentialKernelBound
        (flatGaugeFixedCovarianceCLM ρ (fun i : Empty => i.elim)
          (fun i : Empty => i.elim) ha hP zeroSigma_delta_summable
          zeroSigma_norm_le (zeroSigma_budget ρ ha hP))
        physicalBondDist (2 / (min 1 a / CP)) θ := by
  obtain ⟨θ, hθ, hb⟩ :=
    exists_pos_tiltBudget (3 * L) ((2 * (3 * L + 1)) ^ d * d)
      (M := (((4 * d : ℕ) : ℝ) ^ 2 + (2 : ℝ) ^ 2) + |a| * (L : ℝ) ^ 2)
      (by positivity)
      (div_pos (lt_min one_pos ha) hP.1)
  exact ⟨θ, hθ, flatGaugeFixedCovariance_CT_fixedVolume ρ ha hP hθ hb⟩

end YangMills.RG
