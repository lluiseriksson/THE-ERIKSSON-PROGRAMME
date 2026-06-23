/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFHsharpGeometricMajorant

/-!
# Closing scale, order, and target infinities

This module formalizes a small but useful piece of RG bookkeeping suggested by
the "marked infinity" viewpoint: keep the scale index, expansion order, and
rooted target visible until all three budgets have been applied.

The theorem is deliberately abstract.  If a source proof supplies a pointwise
bound

`|H k n Y| <= M * eps k * (Lleaf * eps k)^n * w Y`,

with a uniform leaf budget `Lleaf * eps k <= q < 1`, a rooted target sum
`sum w <= Kroot`, and a nonnegative summable scale budget
`eps k <= A * exp (-(c0 * t)) * scaleWeight k`, then the iterated influence

`sum_k sum_n sum_Y |H k n Y|`

is bounded by the closed scalar constant

`M * A * Kroot * G0 * exp (-(c0 * t)) * (1 - q)^(-1)`.

Honest scope: the module proves only deterministic summation algebra.  It does
not prove the source activity estimate, the rooted target geometry, the scale
coupling bound, or any physical Yang--Mills covariance statement.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No project
assumptions.
-/

namespace YangMills.RG

open scoped BigOperators

/-- For one fixed scale, a root factor times a geometric leaf factor and a
summable target weight close the order and target sums. -/
theorem orderTargetInfluence_le_of_geometric_leaf
    {ι : Type*}
    (H : ℕ → ι → ℝ) (w : ι → ℝ)
    {M eps Lleaf Kroot q : ℝ}
    (hM : 0 ≤ M) (heps : 0 ≤ eps) (hLleaf : 0 ≤ Lleaf)
    (hw_nonneg : ∀ Y : ι, 0 ≤ w Y)
    (hwsum : Summable w) (hwK : ∑' Y : ι, w Y ≤ Kroot)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hleaf : Lleaf * eps ≤ q)
    (hHsummable : ∀ n : ℕ, Summable fun Y : ι => |H n Y|)
    (hnsummable : Summable fun n : ℕ => ∑' Y : ι, |H n Y|)
    (hpoint :
      ∀ (n : ℕ) (Y : ι),
        |H n Y| ≤ M * eps * (Lleaf * eps) ^ n * w Y) :
    (∑' n : ℕ, ∑' Y : ι, |H n Y|)
      ≤ M * eps * Kroot * (1 - q)⁻¹ := by
  have hbase0 : 0 ≤ Lleaf * eps := mul_nonneg hLleaf heps
  have hKroot : 0 ≤ Kroot := (tsum_nonneg hw_nonneg).trans hwK
  have hbase_pow_le : ∀ n : ℕ, (Lleaf * eps) ^ n ≤ q ^ n :=
    fun n => pow_le_pow_left₀ hbase0 hleaf n
  have htarget :
      ∀ n : ℕ, (∑' Y : ι, |H n Y|) ≤ M * eps * Kroot * q ^ n := by
    intro n
    have hcoeff_nonneg : 0 ≤ M * eps * (Lleaf * eps) ^ n :=
      mul_nonneg (mul_nonneg hM heps) (pow_nonneg hbase0 n)
    have htargetMajor :
        Summable fun Y : ι => M * eps * (Lleaf * eps) ^ n * w Y :=
      hwsum.mul_left _
    calc
      (∑' Y : ι, |H n Y|)
          ≤ ∑' Y : ι, M * eps * (Lleaf * eps) ^ n * w Y :=
            (hHsummable n).tsum_le_tsum (fun Y => hpoint n Y) htargetMajor
      _ = (M * eps * (Lleaf * eps) ^ n) * ∑' Y : ι, w Y := by
            rw [tsum_mul_left]
      _ ≤ (M * eps * (Lleaf * eps) ^ n) * Kroot :=
            mul_le_mul_of_nonneg_left hwK hcoeff_nonneg
      _ = M * eps * Kroot * (Lleaf * eps) ^ n := by ring
      _ ≤ M * eps * Kroot * q ^ n :=
            mul_le_mul_of_nonneg_left (hbase_pow_le n)
              (mul_nonneg (mul_nonneg hM heps) hKroot)
  have hmajor :
      Summable fun n : ℕ => M * eps * Kroot * q ^ n :=
    summable_geometric_majorant (A := M * eps * Kroot) hq0 hq1
  calc
    (∑' n : ℕ, ∑' Y : ι, |H n Y|)
        ≤ ∑' n : ℕ, M * eps * Kroot * q ^ n :=
          hnsummable.tsum_le_tsum htarget hmajor
    _ = M * eps * Kroot * (1 - q)⁻¹ :=
          tsum_geometric_majorant (A := M * eps * Kroot) hq0 hq1

/-- Once each scale has the closed order-target bound, a summable scale budget
closes the remaining scale sum. -/
theorem scaleInfluence_le_of_scale_budget
    (perScale eps scaleWeight : ℕ → ℝ)
    {M A Kroot G0 c0 q t : ℝ}
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hKroot : 0 ≤ Kroot)
    (hscale_nonneg : ∀ k : ℕ, 0 ≤ scaleWeight k)
    (hscale_sum : Summable scaleWeight)
    (hscale_bound : ∑' k : ℕ, scaleWeight k ≤ G0)
    (hq1 : q < 1)
    (heps_le :
      ∀ k : ℕ,
        eps k ≤ A * Real.exp (-(c0 * t)) * scaleWeight k)
    (hk_summable : Summable perScale)
    (hper :
      ∀ k : ℕ, perScale k ≤ M * eps k * Kroot * (1 - q)⁻¹) :
    (∑' k : ℕ, perScale k)
      ≤ M * A * Kroot * G0 * Real.exp (-(c0 * t)) * (1 - q)⁻¹ := by
  have hinv_nonneg : 0 ≤ (1 - q)⁻¹ := by
    exact inv_nonneg.mpr (sub_nonneg.mpr hq1.le)
  have hcoeff_nonneg : 0 ≤ M * Kroot * (1 - q)⁻¹ :=
    mul_nonneg (mul_nonneg hM hKroot) hinv_nonneg
  have hamp_nonneg : 0 ≤ A * Real.exp (-(c0 * t)) :=
    mul_nonneg hA (Real.exp_pos _).le
  have hbig_coeff_nonneg :
      0 ≤ M * A * Kroot * Real.exp (-(c0 * t)) * (1 - q)⁻¹ := by
    positivity
  have _hscale_target_nonneg :
      0 ≤
        M * A * Kroot * G0 * Real.exp (-(c0 * t)) * (1 - q)⁻¹ := by
    have hG0 : 0 ≤ G0 := (tsum_nonneg hscale_nonneg).trans hscale_bound
    positivity
  have hterm :
      ∀ k : ℕ,
        perScale k ≤
          (M * A * Kroot * Real.exp (-(c0 * t)) * (1 - q)⁻¹) *
            scaleWeight k := by
    intro k
    calc
      perScale k
          ≤ M * eps k * Kroot * (1 - q)⁻¹ := hper k
      _ = (M * Kroot * (1 - q)⁻¹) * eps k := by ring
      _ ≤ (M * Kroot * (1 - q)⁻¹) *
            (A * Real.exp (-(c0 * t)) * scaleWeight k) :=
            mul_le_mul_of_nonneg_left (heps_le k) hcoeff_nonneg
      _ = (M * A * Kroot * Real.exp (-(c0 * t)) * (1 - q)⁻¹) *
            scaleWeight k := by ring
  have hmajor :
      Summable fun k : ℕ =>
        (M * A * Kroot * Real.exp (-(c0 * t)) * (1 - q)⁻¹) *
          scaleWeight k :=
    hscale_sum.mul_left _
  calc
    (∑' k : ℕ, perScale k)
        ≤ ∑' k : ℕ,
            (M * A * Kroot * Real.exp (-(c0 * t)) * (1 - q)⁻¹) *
              scaleWeight k :=
          hk_summable.tsum_le_tsum hterm hmajor
    _ = (M * A * Kroot * Real.exp (-(c0 * t)) * (1 - q)⁻¹) *
          ∑' k : ℕ, scaleWeight k := by
          rw [tsum_mul_left]
    _ ≤ (M * A * Kroot * Real.exp (-(c0 * t)) * (1 - q)⁻¹) * G0 :=
          mul_le_mul_of_nonneg_left hscale_bound hbig_coeff_nonneg
    _ = M * A * Kroot * G0 * Real.exp (-(c0 * t)) * (1 - q)⁻¹ := by ring

/-- The full three-infinity closure: expansion order, rooted target geometry,
and scale all sum to one explicit influence bound. -/
theorem tripleInfluence_le_of_geometric_leaf_scale_budget
    {ι : Type*}
    (H : ℕ → ℕ → ι → ℝ) (w : ι → ℝ)
    (eps scaleWeight : ℕ → ℝ)
    {M Lleaf A Kroot G0 c0 q t : ℝ}
    (hM : 0 ≤ M) (hLleaf : 0 ≤ Lleaf) (hA : 0 ≤ A)
    (hw_nonneg : ∀ Y : ι, 0 ≤ w Y)
    (hwsum : Summable w) (hwK : ∑' Y : ι, w Y ≤ Kroot)
    (hscale_nonneg : ∀ k : ℕ, 0 ≤ scaleWeight k)
    (hscale_sum : Summable scaleWeight)
    (hscale_bound : ∑' k : ℕ, scaleWeight k ≤ G0)
    (heps_nonneg : ∀ k : ℕ, 0 ≤ eps k)
    (heps_le :
      ∀ k : ℕ,
        eps k ≤ A * Real.exp (-(c0 * t)) * scaleWeight k)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hleaf : ∀ k : ℕ, Lleaf * eps k ≤ q)
    (hYsummable :
      ∀ k n : ℕ, Summable fun Y : ι => |H k n Y|)
    (hn_summable :
      ∀ k : ℕ, Summable fun n : ℕ => ∑' Y : ι, |H k n Y|)
    (hk_summable :
      Summable fun k : ℕ => ∑' n : ℕ, ∑' Y : ι, |H k n Y|)
    (hpoint :
      ∀ (k n : ℕ) (Y : ι),
        |H k n Y| ≤ M * eps k * (Lleaf * eps k) ^ n * w Y) :
    (∑' k : ℕ, ∑' n : ℕ, ∑' Y : ι, |H k n Y|)
      ≤ M * A * Kroot * G0 * Real.exp (-(c0 * t)) * (1 - q)⁻¹ := by
  have hKroot : 0 ≤ Kroot := (tsum_nonneg hw_nonneg).trans hwK
  have hper :
      ∀ k : ℕ,
        (∑' n : ℕ, ∑' Y : ι, |H k n Y|)
          ≤ M * eps k * Kroot * (1 - q)⁻¹ := by
    intro k
    exact orderTargetInfluence_le_of_geometric_leaf
      (H := H k) (w := w)
      hM (heps_nonneg k) hLleaf hw_nonneg hwsum hwK hq0 hq1
      (hleaf k) (hYsummable k) (hn_summable k) (hpoint k)
  exact scaleInfluence_le_of_scale_budget
    (perScale := fun k : ℕ => ∑' n : ℕ, ∑' Y : ι, |H k n Y|)
    (eps := eps) (scaleWeight := scaleWeight)
    hM hA hKroot hscale_nonneg hscale_sum hscale_bound hq1
    heps_le hk_summable hper

end YangMills.RG
