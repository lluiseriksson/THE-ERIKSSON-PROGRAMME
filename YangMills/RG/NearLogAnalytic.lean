/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.NearLogTermFDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Analyticity of the noncommutative near-identity logarithm

The Mercator series defining `nearLog` is already known to converge on the
open unit ball and to possess its termwise first derivative there.  This file
packages the same series as a `FormalMultilinearSeries`.  Its radius is at
least one, so Mathlib's analytic calculus becomes available at every point
with norm strictly less than one.

This packaging is needed for the genuine second-order Taylor remainder in
CMP98 (123); it does not introduce a smoothness assumption on `nearLog`.
-/

namespace YangMills.RG

open Filter ENNReal
open scoped NNReal

noncomputable section

variable {𝔸 : Type*}
variable [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The formal noncommutative Mercator series. -/
def nearLogFPowerSeries : FormalMultilinearSeries ℝ 𝔸 𝔸 :=
  FormalMultilinearSeries.ofScalars 𝔸 logCoeff

/-- The Mercator formal series has radius of convergence at least one. -/
theorem nearLogFPowerSeries_radius_ge_one [NormOneClass 𝔸] :
    (1 : ℝ≥0∞) ≤ (nearLogFPowerSeries (𝔸 := 𝔸)).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  have hr1 : (r : ℝ) < 1 := by
    exact_mod_cast hr
  have hgeo : Summable (fun n : ℕ => (r : ℝ) ^ n) :=
    summable_geometric_of_lt_one r.coe_nonneg hr1
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  refine Summable.of_norm_bounded hgeo ?_
  intro n
  rw [nearLogFPowerSeries, FormalMultilinearSeries.ofScalars_norm]
  rw [Real.norm_eq_abs]
  rw [abs_of_nonneg
    (mul_nonneg (norm_nonneg (logCoeff n)) (pow_nonneg r.coe_nonneg n))]
  simpa [Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_right (abs_logCoeff_le_one n)
      (pow_nonneg r.coe_nonneg n)

/-- The defining function `nearLog` is represented by its Mercator formal
power series on the full radius supplied by that series. -/
theorem hasFPowerSeriesOnBall_nearLog [NormOneClass 𝔸] :
    HasFPowerSeriesOnBall (nearLog : 𝔸 → 𝔸)
      (nearLogFPowerSeries (𝔸 := 𝔸)) 0
      (nearLogFPowerSeries (𝔸 := 𝔸)).radius := by
  have hr : 0 < (nearLogFPowerSeries (𝔸 := 𝔸)).radius :=
    zero_lt_one.trans_le nearLogFPowerSeries_radius_ge_one
  have hp :=
    (nearLogFPowerSeries (𝔸 := 𝔸)).hasFPowerSeriesOnBall hr
  have hfun : (nearLogFPowerSeries (𝔸 := 𝔸)).sum =
      (nearLog : 𝔸 → 𝔸) := by
    funext Y
    rw [nearLog, ← FormalMultilinearSeries.ofScalars_sum_eq]
    rfl
  rwa [hfun] at hp

/-- `nearLog` is analytic at every point of the open unit ball. -/
theorem analyticAt_nearLog_of_norm_lt_one [NormOneClass 𝔸]
    {Y : 𝔸} (hY : ‖Y‖ < 1) :
    AnalyticAt ℝ (nearLog : 𝔸 → 𝔸) Y := by
  apply hasFPowerSeriesOnBall_nearLog.analyticAt_of_mem
  rw [mem_eball_zero_iff]
  have hY' : (‖Y‖₊ : ℝ≥0∞) < 1 := by
    exact_mod_cast hY
  exact hY'.trans_le nearLogFPowerSeries_radius_ge_one

end

end YangMills.RG
