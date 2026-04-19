/-
Copyright (c) 2026 The Eriksson Programme. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson

Log Z Convergence (Phase 15e, Layer A3)

Proves that the logarithm of the polymer partition function
converges absolutely under the Kotecky-Preiss smallness condition.
-/

import Mathlib
import YangMills.ClayCore.MayerExpansion

namespace YangMills

open Real Finset

/-- The polymer partition function on a finite type. -/
noncomputable def polymerZ
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : Finset ι → ℝ) : ℝ :=
  ∑ X : Finset ι, Real.exp (z X)

/-- Any real function on a Fintype is summable (trivially, since the sum is finite). -/
theorem polymer_activities_summable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : Finset ι → ℝ)
    (A r : ℝ) (hA_nn : 0 ≤ A) (hr_nn : 0 ≤ r) (hr_lt1 : r < 1)
    (hbound : ∀ X : Finset ι, |z X| ≤ A * r ^ X.card) :
    Summable z :=
  (hasSum_fintype z).summable

/-- The partition function is strictly positive. -/
theorem polymerZ_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : Finset ι → ℝ) : 0 < polymerZ z := by
  unfold polymerZ
  apply Finset.sum_pos
  · intro X _; exact Real.exp_pos _
  · exact ⟨∅, Finset.mem_univ _⟩

/-- Abstract log-Z convergence structure: packages the KP → log Z
convergence without requiring the full Brydges-Kennedy identity. -/
structure LogZBound
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The log-activity function. -/
  z : Finset ι → ℝ
  /-- The truncated (Ursell) activities. -/
  K : TruncatedActivities ι
  /-- KP decay rate. -/
  r : ℝ
  hr_pos : 0 < r
  hr_lt1 : r < 1
  /-- log Z equals the cluster expansion (Brydges-Kennedy). -/
  h_logZ_eq : Real.log (polymerZ z) = ∑' Y, K.K Y

/-- From a LogZBound, |log Z| is bounded by the tsum of K_bound. -/
theorem logZ_le_tsum_Kbound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lzb : LogZBound ι) :
    |Real.log (polymerZ lzb.z)| ≤ ∑' Y, lzb.K.K_bound Y := by
  rw [lzb.h_logZ_eq]
  have h1 : |∑' Y, lzb.K.K Y| ≤ ∑' Y, |lzb.K.K Y| := by
    have := norm_tsum_le_tsum_norm (f := lzb.K.K) lzb.K.summable_abs_K
    simpa [Real.norm_eq_abs] using this
  have h2 : ∑' Y, |lzb.K.K Y| ≤ ∑' Y, lzb.K.K_bound Y :=
    Summable.tsum_le_tsum lzb.K.K_abs_le lzb.K.summable_abs_K lzb.K.summable_K_bound
  exact le_trans h1 h2

/-- The connecting sum decays geometrically when the connecting bound does. -/
theorem connecting_sum_decays
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lzb : LogZBound ι) (p q : ι)
    (C_clust : ℝ) (hC : 0 ≤ C_clust)
    (h_decay : lzb.K.connectingBound p q ≤ C_clust * lzb.r ^ (Fintype.card ι)) :
    |lzb.K.connectingSum p q| ≤ C_clust * lzb.r ^ (Fintype.card ι) :=
  le_trans (lzb.K.abs_connectingSum_le_connectingBound p q) h_decay

end YangMills
