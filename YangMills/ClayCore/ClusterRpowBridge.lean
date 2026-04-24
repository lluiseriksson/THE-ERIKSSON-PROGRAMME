/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.ClayCore.MayerExpansion
import YangMills.ClayCore.WilsonClusterProof
import YangMills.ClayCore.ConnectingClusterCount
import YangMills.ClayCore.ConnectedCorrDecay

/-!
# Cluster rpow bridge

Composes the two existing F3 ingredients:

* `TruncatedActivities.abs_connectingSum_le_connectingBound`
  from `MayerExpansion.lean`;
* `connecting_cluster_tsum_le` from `ClusterSeriesBound.lean`.

The result is the public bridge from a cluster-series bound to the
`C * r^dist` shape consumed by the `h_rpow` frontier.

No sorry. No new axioms.
-/

namespace YangMills

open scoped Classical

namespace TruncatedActivities

open Real

/-- **F3 rpow bridge.** If the abstract connecting bound is controlled by
the standard connecting-cluster series

`∑ n, C_conn * n^dim * A₀ * r^(n + dist)`,

then the signed connecting sum is controlled by the factored rpow shape

`clusterPrefactor r C_conn A₀ dim * r^dist`.

This is the exact analytic shape needed before instantiating the
Wilson connected correlator side of `h_rpow`. -/
theorem two_point_decay_from_cluster_tsum
    {ι : Type*} [DecidableEq ι]
    (T : TruncatedActivities ι) (p q : ι)
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim dist : ℕ)
    (h_bound : T.connectingBound p q ≤
      ∑' n : ℕ, C_conn * (n : ℝ) ^ dim * A₀ * r ^ (n + dist)) :
    |T.connectingSum p q| ≤
      clusterPrefactor r C_conn A₀ dim * r ^ dist := by
  have h_factored :
      ∑' n : ℕ, C_conn * (n : ℝ) ^ dim * A₀ * r ^ (n + dist) =
        clusterPrefactor r C_conn A₀ dim * r ^ dist :=
    connecting_cluster_tsum_le r hr_pos hr_lt1 C_conn A₀ hC hA dim dist
  exact (T.abs_connectingSum_le_connectingBound p q).trans
    (h_bound.trans_eq h_factored)

/-- Shifted KP-series variant of `two_point_decay_from_cluster_tsum`. -/
theorem two_point_decay_from_cluster_tsum_shifted
    {ι : Type*} [DecidableEq ι]
    (T : TruncatedActivities ι) (p q : ι)
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim dist : ℕ)
    (h_bound : T.connectingBound p q ≤
      ∑' n : ℕ, C_conn * (((n + 1 : ℕ) : ℝ) ^ dim) * A₀ *
        r ^ (n + dist)) :
    |T.connectingSum p q| ≤
      clusterPrefactorShifted r C_conn A₀ dim * r ^ dist := by
  have h_factored :
      ∑' n : ℕ, C_conn * (((n + 1 : ℕ) : ℝ) ^ dim) * A₀ *
          r ^ (n + dist) =
        clusterPrefactorShifted r C_conn A₀ dim * r ^ dist :=
    connecting_cluster_tsum_le_shifted r hr_pos hr_lt1 C_conn A₀ hC hA dim dist
  exact (T.abs_connectingSum_le_connectingBound p q).trans
    (h_bound.trans_eq h_factored)

#print axioms TruncatedActivities.two_point_decay_from_cluster_tsum
#print axioms TruncatedActivities.two_point_decay_from_cluster_tsum_shifted

end TruncatedActivities

/-! ### Wilson-facing F3 bridge -/

/-- **F3 Wilson bridge.**  A Wilson connected correlator bound follows from
three explicit inputs:

* a Mayer/Ursell identity identifying the Wilson connected correlator with
  the connecting truncated-activity sum;
* a Kotecky-Preiss connecting-cluster series bound on `connectingBound`;
* a final geometric comparison from the discrete cluster distance `distNat`
  to the lattice distance used by `ClusterCorrelatorBound`.

This theorem is deliberately honest about the remaining analytic work: the
Mayer identity and geometric comparison are supplied as hypotheses, while the
summability/factoring step is fully discharged by `two_point_decay_from_cluster_tsum`. -/
theorem clusterCorrelatorBound_of_truncatedActivities
    (N_c : ℕ) [NeZero N_c]
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ)
    (T : ∀ {d L : ℕ} [NeZero d] [NeZero L],
      (β : ℝ) →
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) →
      ConcretePlaquette d L → ConcretePlaquette d L →
      TruncatedActivities (ConcretePlaquette d L))
    (distNat : ∀ {d L : ℕ} [NeZero d] [NeZero L],
      (β : ℝ) →
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) →
      ConcretePlaquette d L → ConcretePlaquette d L → ℕ)
    (h_mayer : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q =
      (T β F p q).connectingSum p q)
    (h_bound : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      (T β F p q).connectingBound p q ≤
        ∑' n : ℕ, C_conn * (n : ℝ) ^ dim * A₀ *
          r ^ (n + distNat β F p q))
    (h_geom : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      clusterPrefactor r C_conn A₀ dim * r ^ (distNat β F p q) ≤
        clusterPrefactor r C_conn A₀ dim *
          Real.exp (-(kpParameter r) * siteLatticeDist p.site q.site)) :
    ClusterCorrelatorBound N_c r (clusterPrefactor r C_conn A₀ dim) := by
  intro d L _ _ β hβ F hF p q hdist
  rw [h_mayer β hβ F hF p q hdist]
  exact ((T β F p q).two_point_decay_from_cluster_tsum p q
    r hr_pos hr_lt1 C_conn A₀ hC hA dim (distNat β F p q)
    (h_bound β hβ F hF p q hdist)).trans
      (h_geom β hβ F hF p q hdist)

#print axioms clusterCorrelatorBound_of_truncatedActivities

/-- Geometric comparison for the canonical discrete cluster distance
`⌈x⌉₊`: the factored `r^⌈x⌉₊` bound is already strong enough for the
`ClusterCorrelatorBound` exponential target. -/
theorem clusterPrefactor_rpow_ceil_le_exp
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ) (x : ℝ) :
    clusterPrefactor r C_conn A₀ dim * r ^ (⌈x⌉₊) ≤
      clusterPrefactor r C_conn A₀ dim *
        Real.exp (-(kpParameter r) * x) := by
  have hpref_nonneg :
      0 ≤ clusterPrefactor r C_conn A₀ dim :=
    (clusterPrefactor_pos r hr_pos hr_lt1 C_conn A₀ hC hA dim).le
  apply mul_le_mul_of_nonneg_left ?_ hpref_nonneg
  have hceil : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have hceil_nonneg : 0 ≤ (⌈x⌉₊ : ℝ) := by exact_mod_cast Nat.zero_le ⌈x⌉₊
  have hkp_pos : 0 < kpParameter r := kpParameter_pos hr_pos hr_lt1
  have hceil_exp :
      r ^ ((⌈x⌉₊ : ℝ)) ≤ Real.exp (-(kpParameter r) * (⌈x⌉₊ : ℝ)) :=
    rpow_le_exp_kpParameter hr_pos hr_lt1 hceil_nonneg
  have hexp_mono :
      Real.exp (-(kpParameter r) * (⌈x⌉₊ : ℝ)) ≤
        Real.exp (-(kpParameter r) * x) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hceil hkp_pos.le]
  calc
    r ^ (⌈x⌉₊)
        = r ^ ((⌈x⌉₊ : ℝ)) := by rw [Real.rpow_natCast]
    _ ≤ Real.exp (-(kpParameter r) * (⌈x⌉₊ : ℝ)) := hceil_exp
    _ ≤ Real.exp (-(kpParameter r) * x) := hexp_mono

/-- Shifted-prefactor variant of `clusterPrefactor_rpow_ceil_le_exp`. -/
theorem clusterPrefactorShifted_rpow_ceil_le_exp
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ) (x : ℝ) :
    clusterPrefactorShifted r C_conn A₀ dim * r ^ (⌈x⌉₊) ≤
      clusterPrefactorShifted r C_conn A₀ dim *
        Real.exp (-(kpParameter r) * x) := by
  have hpref_nonneg :
      0 ≤ clusterPrefactorShifted r C_conn A₀ dim :=
    (clusterPrefactorShifted_pos r hr_pos hr_lt1 C_conn A₀ hC hA dim).le
  apply mul_le_mul_of_nonneg_left ?_ hpref_nonneg
  have hceil : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have hceil_nonneg : 0 ≤ (⌈x⌉₊ : ℝ) := by exact_mod_cast Nat.zero_le ⌈x⌉₊
  have hkp_pos : 0 < kpParameter r := kpParameter_pos hr_pos hr_lt1
  have hceil_exp :
      r ^ ((⌈x⌉₊ : ℝ)) ≤ Real.exp (-(kpParameter r) * (⌈x⌉₊ : ℝ)) :=
    rpow_le_exp_kpParameter hr_pos hr_lt1 hceil_nonneg
  have hexp_mono :
      Real.exp (-(kpParameter r) * (⌈x⌉₊ : ℝ)) ≤
        Real.exp (-(kpParameter r) * x) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hceil hkp_pos.le]
  calc
    r ^ (⌈x⌉₊)
        = r ^ ((⌈x⌉₊ : ℝ)) := by rw [Real.rpow_natCast]
    _ ≤ Real.exp (-(kpParameter r) * (⌈x⌉₊ : ℝ)) := hceil_exp
    _ ≤ Real.exp (-(kpParameter r) * x) := hexp_mono

/-- Canonical-ceiling version of `clusterCorrelatorBound_of_truncatedActivities`.
Here the discrete cluster distance is fixed to `⌈siteLatticeDist⌉₊`, so the
geometric comparison is proved internally by
`clusterPrefactor_rpow_ceil_le_exp`. -/
theorem clusterCorrelatorBound_of_truncatedActivities_ceil
    (N_c : ℕ) [NeZero N_c]
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ)
    (T : ∀ {d L : ℕ} [NeZero d] [NeZero L],
      (β : ℝ) →
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) →
      ConcretePlaquette d L → ConcretePlaquette d L →
      TruncatedActivities (ConcretePlaquette d L))
    (h_mayer : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q =
      (T β F p q).connectingSum p q)
    (h_bound : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      (T β F p q).connectingBound p q ≤
        ∑' n : ℕ, C_conn * (n : ℝ) ^ dim * A₀ *
          r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊)) :
    ClusterCorrelatorBound N_c r (clusterPrefactor r C_conn A₀ dim) := by
  refine clusterCorrelatorBound_of_truncatedActivities
    N_c r hr_pos hr_lt1 C_conn A₀ hC hA dim T
    (fun β F p q => ⌈siteLatticeDist p.site q.site⌉₊)
    h_mayer h_bound ?_
  intro d L _ _ β hβ F hF p q hdist
  exact clusterPrefactor_rpow_ceil_le_exp
    r hr_pos hr_lt1 C_conn A₀ hC hA dim (siteLatticeDist p.site q.site)

/-- Shifted KP-series version of
`clusterCorrelatorBound_of_truncatedActivities_ceil`. -/
theorem clusterCorrelatorBound_of_truncatedActivities_ceil_shifted
    (N_c : ℕ) [NeZero N_c]
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ)
    (T : ∀ {d L : ℕ} [NeZero d] [NeZero L],
      (β : ℝ) →
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) →
      ConcretePlaquette d L → ConcretePlaquette d L →
      TruncatedActivities (ConcretePlaquette d L))
    (h_mayer : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q =
      (T β F p q).connectingSum p q)
    (h_bound : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      (T β F p q).connectingBound p q ≤
        ∑' n : ℕ, C_conn * (((n + 1 : ℕ) : ℝ) ^ dim) * A₀ *
          r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊)) :
    ClusterCorrelatorBound N_c r
      (clusterPrefactorShifted r C_conn A₀ dim) := by
  intro d L _ _ β hβ F hF p q hdist
  rw [h_mayer β hβ F hF p q hdist]
  exact ((T β F p q).two_point_decay_from_cluster_tsum_shifted p q
    r hr_pos hr_lt1 C_conn A₀ hC hA dim
    ⌈siteLatticeDist p.site q.site⌉₊
    (h_bound β hβ F hF p q hdist)).trans
    (clusterPrefactorShifted_rpow_ceil_le_exp
      r hr_pos hr_lt1 C_conn A₀ hC hA dim (siteLatticeDist p.site q.site))

/-- Finite-sum version of `clusterCorrelatorBound_of_truncatedActivities_ceil`.

On the concrete finite plaquette lattice, it is enough to bound the finite
sum of `K_bound` over polymers containing `p` and `q`; the abstract
`connectingBound` is opened internally by
`TruncatedActivities.connectingBound_eq_finset_sum`.  This is the shape
closest to the lattice-animal counting estimate. -/
theorem clusterCorrelatorBound_of_finiteConnectingBounds_ceil
    (N_c : ℕ) [NeZero N_c]
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ)
    (T : ∀ {d L : ℕ} [NeZero d] [NeZero L],
      (β : ℝ) →
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) →
      ConcretePlaquette d L → ConcretePlaquette d L →
      TruncatedActivities (ConcretePlaquette d L))
    (h_mayer : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q =
      (T β F p q).connectingSum p q)
    (h_finite_bound : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      (∑ Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
          (fun Y => p ∈ Y ∧ q ∈ Y),
        (T β F p q).K_bound Y) ≤
        ∑' n : ℕ, C_conn * (n : ℝ) ^ dim * A₀ *
          r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊)) :
    ClusterCorrelatorBound N_c r (clusterPrefactor r C_conn A₀ dim) := by
  refine clusterCorrelatorBound_of_truncatedActivities_ceil
    N_c r hr_pos hr_lt1 C_conn A₀ hC hA dim T h_mayer ?_
  intro d L _ _ β hβ F hF p q hdist
  rw [(T β F p q).connectingBound_eq_finset_sum p q]
  exact h_finite_bound β hβ F hF p q hdist

#print axioms clusterPrefactor_rpow_ceil_le_exp
#print axioms clusterPrefactorShifted_rpow_ceil_le_exp
#print axioms clusterCorrelatorBound_of_truncatedActivities_ceil
#print axioms clusterCorrelatorBound_of_truncatedActivities_ceil_shifted
#print axioms clusterCorrelatorBound_of_finiteConnectingBounds_ceil

/-- If `K_bound` vanishes on disconnected polymers containing `p` and `q`,
then the finite connecting sum may be restricted to connected polymers.
This is the support/cancellation shape used before applying lattice-animal
counting. -/
theorem finiteConnectingSum_eq_connectedFiniteSum
    {d L : ℕ} [NeZero d] [NeZero L]
    (K_bound : Finset (ConcretePlaquette d L) → ℝ)
    (p q : ConcretePlaquette d L)
    (h_zero : ∀ Y : Finset (ConcretePlaquette d L), p ∈ Y → q ∈ Y →
      ¬ PolymerConnected Y → K_bound Y = 0) :
    (∑ Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun Y => p ∈ Y ∧ q ∈ Y), K_bound Y) =
      ∑ Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun Y => p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y), K_bound Y := by
  classical
  rw [Finset.sum_filter]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Y _
  by_cases hpq : p ∈ Y ∧ q ∈ Y
  · by_cases hconn : PolymerConnected Y
    · simp [hpq, hconn]
    · simp [hpq, hconn, h_zero Y hpq.1 hpq.2 hconn]
  · simp [hpq]
    intro hp hq _
    exact (hpq ⟨hp, hq⟩).elim

/-- Connected finite sums decompose into the canonical cardinality buckets
`Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊`.

The outer range is finite because the polymer universe is finite; buckets
outside the possible cardinalities contribute zero. This is the exact finite
combinatorial form that precedes a lattice-animal bound. -/
theorem connectedFiniteSum_eq_cardBucketSum
    {d L : ℕ} [NeZero d] [NeZero L]
    (K_bound : Finset (ConcretePlaquette d L) → ℝ)
    (p q : ConcretePlaquette d L) :
    (∑ Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun Y => p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y), K_bound Y) =
      Finset.sum
        (Finset.range (Fintype.card (ConcretePlaquette d L) + 1))
        (fun n =>
        (∑ Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
          (fun Y => p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y),
          if Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊
            then K_bound Y else 0)) := by
  classical
  let S := (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
    (fun Y => p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y)
  let c := ⌈siteLatticeDist p.site q.site⌉₊
  let M := Fintype.card (ConcretePlaquette d L)
  have h_pointwise : ∀ Y ∈ S,
      K_bound Y =
        Finset.sum (Finset.range (M + 1))
          (fun n => if Y.card = n + c then K_bound Y else 0) := by
    intro Y hY
    have hY' :
        p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y := by
      simpa [S] using (Finset.mem_filter.mp hY).2
    have hc_le : c ≤ Y.card := by
      simpa [c] using
        ceil_siteLatticeDist_le_polymer_card p q Y hY'.1 hY'.2.1 hY'.2.2
    have hcard_le : Y.card ≤ M := by
      simpa [M] using Finset.card_le_univ Y
    have hn_mem : Y.card - c ∈ Finset.range (M + 1) := by
      rw [Finset.mem_range]
      omega
    have h_eq : Y.card = (Y.card - c) + c := (Nat.sub_add_cancel hc_le).symm
    symm
    rw [Finset.sum_eq_single (Y.card - c)]
    · rw [if_pos h_eq]
    · intro n hn hne
      by_cases hn_eq : Y.card = n + c
      · have : n = Y.card - c := by omega
        exact (hne this).elim
      · rw [if_neg hn_eq]
    · intro hnot
      exact (hnot hn_mem).elim
  calc
    (∑ Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun Y => p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y), K_bound Y)
        = Finset.sum S (fun Y => K_bound Y) := by simp [S]
    _ = Finset.sum S (fun Y => Finset.sum (Finset.range (M + 1))
          (fun n => if Y.card = n + c then K_bound Y else 0)) := by
        exact Finset.sum_congr rfl h_pointwise
    _ = Finset.sum (Finset.range (M + 1)) (fun n =>
          Finset.sum S (fun Y => if Y.card = n + c then K_bound Y else 0)) := by
        rw [Finset.sum_comm]
    _ = Finset.sum
        (Finset.range (Fintype.card (ConcretePlaquette d L) + 1))
        (fun n =>
        (∑ Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
          (fun Y => p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y),
          if Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊
            then K_bound Y else 0)) := by
        simp [S, M, c]

/-- Bucket-bound consumer for the connected finite sum.

After `connectedFiniteSum_eq_cardBucketSum`, it is enough to bound each
cardinality bucket by the corresponding KP summand and compare the resulting
finite partial sum with the infinite KP series. -/
theorem connectedFiniteSum_le_of_cardBucketBounds
    {d L : ℕ} [NeZero d] [NeZero L]
    (K_bound : Finset (ConcretePlaquette d L) → ℝ)
    (p q : ConcretePlaquette d L)
    (r C_conn A₀ : ℝ) (dim : ℕ)
    (h_bucket : ∀ n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1),
      (∑ Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
          (fun Y => p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y),
          if Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊
            then K_bound Y else 0) ≤
        C_conn * (n : ℝ) ^ dim * A₀ *
          r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊))
    (h_partial_le_tsum :
      Finset.sum (Finset.range (Fintype.card (ConcretePlaquette d L) + 1))
        (fun n => C_conn * (n : ℝ) ^ dim * A₀ *
          r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊)) ≤
        ∑' n : ℕ, C_conn * (n : ℝ) ^ dim * A₀ *
          r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊)) :
    (∑ Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun Y => p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y), K_bound Y) ≤
      ∑' n : ℕ, C_conn * (n : ℝ) ^ dim * A₀ *
        r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊) := by
  rw [connectedFiniteSum_eq_cardBucketSum K_bound p q]
  exact (Finset.sum_le_sum h_bucket).trans h_partial_le_tsum

/-- Shifted bucket-bound consumer for the connected finite sum. -/
theorem connectedFiniteSum_le_of_cardBucketBounds_shifted
    {d L : ℕ} [NeZero d] [NeZero L]
    (K_bound : Finset (ConcretePlaquette d L) → ℝ)
    (p q : ConcretePlaquette d L)
    (r C_conn A₀ : ℝ) (dim : ℕ)
    (h_bucket : ∀ n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1),
      (∑ Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
          (fun Y => p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y),
          if Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊
            then K_bound Y else 0) ≤
        C_conn * (((n + 1 : ℕ) : ℝ) ^ dim) * A₀ *
          r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊))
    (h_partial_le_tsum :
      Finset.sum (Finset.range (Fintype.card (ConcretePlaquette d L) + 1))
        (fun n => C_conn * (((n + 1 : ℕ) : ℝ) ^ dim) * A₀ *
          r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊)) ≤
        ∑' n : ℕ, C_conn * (((n + 1 : ℕ) : ℝ) ^ dim) * A₀ *
          r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊)) :
    (∑ Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun Y => p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y), K_bound Y) ≤
      ∑' n : ℕ, C_conn * (((n + 1 : ℕ) : ℝ) ^ dim) * A₀ *
        r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊) := by
  rw [connectedFiniteSum_eq_cardBucketSum K_bound p q]
  exact (Finset.sum_le_sum h_bucket).trans h_partial_le_tsum

/-- Bucket-bound consumer with the KP partial-sum comparison discharged
internally by `connecting_cluster_partial_sum_le_tsum`. -/
theorem connectedFiniteSum_le_of_cardBucketBounds_kp
    {d L : ℕ} [NeZero d] [NeZero L]
    (K_bound : Finset (ConcretePlaquette d L) → ℝ)
    (p q : ConcretePlaquette d L)
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ)
    (h_bucket : ∀ n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1),
      (∑ Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
          (fun Y => p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y),
          if Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊
            then K_bound Y else 0) ≤
        C_conn * (n : ℝ) ^ dim * A₀ *
          r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊)) :
    (∑ Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun Y => p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y), K_bound Y) ≤
      ∑' n : ℕ, C_conn * (n : ℝ) ^ dim * A₀ *
        r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊) := by
  exact connectedFiniteSum_le_of_cardBucketBounds K_bound p q r C_conn A₀ dim
    h_bucket
    (connecting_cluster_partial_sum_le_tsum r hr_pos hr_lt1 C_conn A₀ hC hA
      dim ⌈siteLatticeDist p.site q.site⌉₊
      (Fintype.card (ConcretePlaquette d L) + 1))

/-- Shifted bucket-bound consumer with the KP partial-sum comparison
discharged internally by `connecting_cluster_partial_sum_le_tsum_shifted`. -/
theorem connectedFiniteSum_le_of_cardBucketBounds_kp_shifted
    {d L : ℕ} [NeZero d] [NeZero L]
    (K_bound : Finset (ConcretePlaquette d L) → ℝ)
    (p q : ConcretePlaquette d L)
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ)
    (h_bucket : ∀ n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1),
      (∑ Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
          (fun Y => p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y),
          if Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊
            then K_bound Y else 0) ≤
        C_conn * (((n + 1 : ℕ) : ℝ) ^ dim) * A₀ *
          r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊)) :
    (∑ Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun Y => p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y), K_bound Y) ≤
      ∑' n : ℕ, C_conn * (((n + 1 : ℕ) : ℝ) ^ dim) * A₀ *
        r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊) := by
  exact connectedFiniteSum_le_of_cardBucketBounds_shifted K_bound p q r C_conn A₀ dim
    h_bucket
    (connecting_cluster_partial_sum_le_tsum_shifted r hr_pos hr_lt1 C_conn A₀ hC hA
      dim ⌈siteLatticeDist p.site q.site⌉₊
      (Fintype.card (ConcretePlaquette d L) + 1))

/-- A single cardinality bucket is bounded by the KP summand if each polymer
in the bucket is bounded by `A₀ * r^(n + ⌈dist⌉₊)` and the number of polymers
in the bucket is bounded by `C_conn * n^dim`. -/
theorem cardBucketSum_le_of_count_and_pointwise
    {d L : ℕ} [NeZero d] [NeZero L]
    (K_bound : Finset (ConcretePlaquette d L) → ℝ)
    (p q : ConcretePlaquette d L)
    (r : ℝ) (hr_pos : 0 < r)
    (C_conn A₀ : ℝ) (hA : 0 < A₀)
    (dim n : ℕ)
    (h_count :
      (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun Y =>
          p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y ∧
            Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
        C_conn * (n : ℝ) ^ dim)
    (h_pointwise : ∀ Y ∈
      (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun Y =>
          p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y ∧
            Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊),
      K_bound Y ≤ A₀ * r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊)) :
    (∑ Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun Y => p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y),
        if Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊
          then K_bound Y else 0) ≤
      C_conn * (n : ℝ) ^ dim * A₀ *
        r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊) := by
  classical
  let S := (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
    (fun Y => p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y)
  let B := (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
    (fun Y =>
      p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y ∧
        Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊)
  let term := A₀ * r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊)
  have hterm_nonneg : 0 ≤ term := by
    exact mul_nonneg hA.le (pow_nonneg hr_pos.le _)
  have hSB :
      S.filter (fun Y => Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊) = B := by
    ext Y
    simp [S, B, and_assoc]
  have h_eq :
      (∑ Y ∈ S,
        if Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊
          then K_bound Y else 0) =
      Finset.sum B (fun Y => K_bound Y) := by
    rw [← Finset.sum_filter]
    rw [hSB]
  calc
    (∑ Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun Y => p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y),
        if Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊
          then K_bound Y else 0)
        = Finset.sum B (fun Y => K_bound Y) := by simpa [S] using h_eq
    _ ≤ Finset.sum B (fun _Y => term) := by
        apply Finset.sum_le_sum
        intro Y hY
        exact h_pointwise Y (by simpa [B] using hY)
    _ = (B.card : ℝ) * term := by
        simp [term, nsmul_eq_mul]
    _ ≤ (C_conn * (n : ℝ) ^ dim) * term := by
        exact mul_le_mul_of_nonneg_right (by simpa [B] using h_count) hterm_nonneg
    _ = C_conn * (n : ℝ) ^ dim * A₀ *
        r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊) := by
        ring

/-- Shifted variant of `cardBucketSum_le_of_count_and_pointwise`, using the
realistic bucket count `C_conn * (n+1)^dim`. -/
theorem cardBucketSum_le_of_count_and_pointwise_shifted
    {d L : ℕ} [NeZero d] [NeZero L]
    (K_bound : Finset (ConcretePlaquette d L) → ℝ)
    (p q : ConcretePlaquette d L)
    (r : ℝ) (hr_pos : 0 < r)
    (C_conn A₀ : ℝ) (hA : 0 < A₀)
    (dim n : ℕ)
    (h_count :
      (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun Y =>
          p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y ∧
            Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
        C_conn * (((n + 1 : ℕ) : ℝ) ^ dim))
    (h_pointwise : ∀ Y ∈
      (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun Y =>
          p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y ∧
            Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊),
      K_bound Y ≤ A₀ * r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊)) :
    (∑ Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun Y => p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y),
        if Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊
          then K_bound Y else 0) ≤
      C_conn * (((n + 1 : ℕ) : ℝ) ^ dim) * A₀ *
        r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊) := by
  classical
  let S := (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
    (fun Y => p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y)
  let B := (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
    (fun Y =>
      p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y ∧
        Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊)
  let term := A₀ * r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊)
  have hterm_nonneg : 0 ≤ term := by
    exact mul_nonneg hA.le (pow_nonneg hr_pos.le _)
  have hSB :
      S.filter (fun Y => Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊) = B := by
    ext Y
    simp [S, B, and_assoc]
  have h_eq :
      (∑ Y ∈ S,
        if Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊
          then K_bound Y else 0) =
      Finset.sum B (fun Y => K_bound Y) := by
    rw [← Finset.sum_filter]
    rw [hSB]
  calc
    (∑ Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun Y => p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y),
        if Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊
          then K_bound Y else 0)
        = Finset.sum B (fun Y => K_bound Y) := by simpa [S] using h_eq
    _ ≤ Finset.sum B (fun _Y => term) := by
        apply Finset.sum_le_sum
        intro Y hY
        exact h_pointwise Y (by simpa [B] using hY)
    _ = (B.card : ℝ) * term := by
        simp [term, nsmul_eq_mul]
    _ ≤ (C_conn * (((n + 1 : ℕ) : ℝ) ^ dim)) * term := by
        exact mul_le_mul_of_nonneg_right (by simpa [B] using h_count) hterm_nonneg
    _ = C_conn * (((n + 1 : ℕ) : ℝ) ^ dim) * A₀ *
        r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊) := by
        ring

/-- Connected finite-sum version of
`clusterCorrelatorBound_of_finiteConnectingBounds_ceil`.

This variant matches the usual KP/lattice-animal input even more closely:
the caller proves that disconnected polymers have zero `K_bound`, and bounds
only the finite connected-polymer sum. -/
theorem clusterCorrelatorBound_of_connectedFiniteBounds_ceil
    (N_c : ℕ) [NeZero N_c]
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ)
    (T : ∀ {d L : ℕ} [NeZero d] [NeZero L],
      (β : ℝ) →
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) →
      ConcretePlaquette d L → ConcretePlaquette d L →
      TruncatedActivities (ConcretePlaquette d L))
    (h_mayer : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q =
      (T β F p q).connectingSum p q)
    (h_zero : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L)
      (Y : Finset (ConcretePlaquette d L)),
      p ∈ Y → q ∈ Y → ¬ PolymerConnected Y →
      (T β F p q).K_bound Y = 0)
    (h_connected_bound : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      (∑ Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
          (fun Y => p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y),
        (T β F p q).K_bound Y) ≤
        ∑' n : ℕ, C_conn * (n : ℝ) ^ dim * A₀ *
          r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊)) :
    ClusterCorrelatorBound N_c r (clusterPrefactor r C_conn A₀ dim) := by
  refine clusterCorrelatorBound_of_finiteConnectingBounds_ceil
    N_c r hr_pos hr_lt1 C_conn A₀ hC hA dim T h_mayer ?_
  intro d L _ _ β hβ F hF p q hdist
  rw [finiteConnectingSum_eq_connectedFiniteSum
    (fun Y => (T β F p q).K_bound Y) p q
    (fun Y hp hq hconn => h_zero β hβ F hF p q Y hp hq hconn)]
  exact h_connected_bound β hβ F hF p q hdist

/-- Bucket-estimate version of
`clusterCorrelatorBound_of_connectedFiniteBounds_ceil`.

This is the closest F3 consumer to the lattice-animal theorem: after the Mayer
identity and disconnected-support cancellation, the caller only bounds each
canonical cardinality bucket. -/
theorem clusterCorrelatorBound_of_cardBucketBounds_ceil
    (N_c : ℕ) [NeZero N_c]
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ)
    (T : ∀ {d L : ℕ} [NeZero d] [NeZero L],
      (β : ℝ) →
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) →
      ConcretePlaquette d L → ConcretePlaquette d L →
      TruncatedActivities (ConcretePlaquette d L))
    (h_mayer : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q =
      (T β F p q).connectingSum p q)
    (h_zero : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L)
      (Y : Finset (ConcretePlaquette d L)),
      p ∈ Y → q ∈ Y → ¬ PolymerConnected Y →
      (T β F p q).K_bound Y = 0)
    (h_bucket : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L)
      (n : ℕ),
      n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1) →
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      (∑ Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
          (fun Y => p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y),
          if Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊
            then (T β F p q).K_bound Y else 0) ≤
        C_conn * (n : ℝ) ^ dim * A₀ *
          r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊)) :
    ClusterCorrelatorBound N_c r (clusterPrefactor r C_conn A₀ dim) := by
  refine clusterCorrelatorBound_of_connectedFiniteBounds_ceil
    N_c r hr_pos hr_lt1 C_conn A₀ hC hA dim T h_mayer h_zero ?_
  intro d L _ _ β hβ F hF p q hdist
  exact connectedFiniteSum_le_of_cardBucketBounds_kp
    (fun Y => (T β F p q).K_bound Y) p q
    r hr_pos hr_lt1 C_conn A₀ hC hA dim
    (fun n hn => h_bucket β hβ F hF p q n hn hdist)

/-- Count-and-pointwise version of the F3 `ClusterCorrelatorBound` bridge.

This composes `cardBucketSum_le_of_count_and_pointwise` with
`clusterCorrelatorBound_of_cardBucketBounds_ceil`.  The caller supplies a
cardinality estimate for each connected bucket and a pointwise `K_bound`
estimate on every polymer in that bucket. -/
theorem clusterCorrelatorBound_of_count_pointwiseBounds_ceil
    (N_c : ℕ) [NeZero N_c]
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ)
    (T : ∀ {d L : ℕ} [NeZero d] [NeZero L],
      (β : ℝ) →
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) →
      ConcretePlaquette d L → ConcretePlaquette d L →
      TruncatedActivities (ConcretePlaquette d L))
    (h_mayer : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q =
      (T β F p q).connectingSum p q)
    (h_zero : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L)
      (Y : Finset (ConcretePlaquette d L)),
      p ∈ Y → q ∈ Y → ¬ PolymerConnected Y →
      (T β F p q).K_bound Y = 0)
    (h_count : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (p q : ConcretePlaquette d L) (n : ℕ),
      n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1) →
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun Y =>
          p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y ∧
            Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
        C_conn * (n : ℝ) ^ dim)
    (h_pointwise : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L)
      (n : ℕ)
      (Y : Finset (ConcretePlaquette d L)),
      n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1) →
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun Y =>
          p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y ∧
            Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊) →
      (T β F p q).K_bound Y ≤
        A₀ * r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊)) :
    ClusterCorrelatorBound N_c r (clusterPrefactor r C_conn A₀ dim) := by
  refine clusterCorrelatorBound_of_cardBucketBounds_ceil
    N_c r hr_pos hr_lt1 C_conn A₀ hC hA dim T h_mayer h_zero ?_
  intro d L _ _ β hβ F hF p q n hn hdist
  exact cardBucketSum_le_of_count_and_pointwise
    (fun Y => (T β F p q).K_bound Y) p q
    r hr_pos C_conn A₀ hA dim n
    (h_count p q n hn hdist)
    (fun Y hY => h_pointwise β hβ F hF p q n Y hn hdist hY)

/-- A global cardinality-decay estimate on `K_bound` restricts to the
corresponding pointwise estimate on a fixed cardinal bucket. -/
theorem pointwiseBucketBound_of_card_decay
    {d L : ℕ} [NeZero d] [NeZero L]
    (K_bound : Finset (ConcretePlaquette d L) → ℝ)
    (p q : ConcretePlaquette d L)
    (r A₀ : ℝ) (n : ℕ)
    (Y : Finset (ConcretePlaquette d L))
    (hY : Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
      (fun Y =>
        p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y ∧
          Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊))
    (h_decay : ∀ Y, K_bound Y ≤ A₀ * r ^ Y.card) :
    K_bound Y ≤ A₀ * r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊) := by
  have hcard :
      Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊ :=
    ((Finset.mem_filter.mp hY).2).2.2.2
  simpa [hcard] using h_decay Y

/-- Count plus global cardinality-decay version of the F3 bridge.

This reduces the previous bucket-wise pointwise input to the more natural
global estimate `(T β F p q).K_bound Y ≤ A₀ * r ^ Y.card`. -/
theorem clusterCorrelatorBound_of_count_cardDecayBounds_ceil
    (N_c : ℕ) [NeZero N_c]
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ)
    (T : ∀ {d L : ℕ} [NeZero d] [NeZero L],
      (β : ℝ) →
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) →
      ConcretePlaquette d L → ConcretePlaquette d L →
      TruncatedActivities (ConcretePlaquette d L))
    (h_mayer : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q =
      (T β F p q).connectingSum p q)
    (h_zero : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L)
      (Y : Finset (ConcretePlaquette d L)),
      p ∈ Y → q ∈ Y → ¬ PolymerConnected Y →
      (T β F p q).K_bound Y = 0)
    (h_count : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (p q : ConcretePlaquette d L) (n : ℕ),
      n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1) →
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun Y =>
          p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y ∧
            Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
        C_conn * (n : ℝ) ^ dim)
    (h_card_decay : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L)
      (Y : Finset (ConcretePlaquette d L)),
      (T β F p q).K_bound Y ≤ A₀ * r ^ Y.card) :
    ClusterCorrelatorBound N_c r (clusterPrefactor r C_conn A₀ dim) := by
  refine clusterCorrelatorBound_of_count_pointwiseBounds_ceil
    N_c r hr_pos hr_lt1 C_conn A₀ hC hA dim T h_mayer h_zero h_count ?_
  intro d L _ _ β hβ F hF p q n Y _hn _hdist hY
  exact pointwiseBucketBound_of_card_decay
    (fun Y => (T β F p q).K_bound Y) p q r A₀ n Y hY
    (fun Y => h_card_decay β hβ F hF p q Y)

/-- Shifted count plus global cardinality-decay version of the F3 bridge.

This consumes the natural bucket count
`#bucket(n) ≤ C_conn * (n+1)^dim`. -/
theorem clusterCorrelatorBound_of_count_cardDecayBounds_ceil_shifted
    (N_c : ℕ) [NeZero N_c]
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ)
    (T : ∀ {d L : ℕ} [NeZero d] [NeZero L],
      (β : ℝ) →
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) →
      ConcretePlaquette d L → ConcretePlaquette d L →
      TruncatedActivities (ConcretePlaquette d L))
    (h_mayer : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q =
      (T β F p q).connectingSum p q)
    (h_zero : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L)
      (Y : Finset (ConcretePlaquette d L)),
      p ∈ Y → q ∈ Y → ¬ PolymerConnected Y →
      (T β F p q).K_bound Y = 0)
    (h_count : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (p q : ConcretePlaquette d L) (n : ℕ),
      n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1) →
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun Y =>
          p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y ∧
            Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
        C_conn * (((n + 1 : ℕ) : ℝ) ^ dim))
    (h_card_decay : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L)
      (Y : Finset (ConcretePlaquette d L)),
      (T β F p q).K_bound Y ≤ A₀ * r ^ Y.card) :
    ClusterCorrelatorBound N_c r
      (clusterPrefactorShifted r C_conn A₀ dim) := by
  refine clusterCorrelatorBound_of_truncatedActivities_ceil_shifted
    N_c r hr_pos hr_lt1 C_conn A₀ hC hA dim T h_mayer ?_
  intro d L _ _ β hβ F hF p q hdist
  have h_connected :
      (∑ Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
          (fun Y => p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y),
        (T β F p q).K_bound Y) ≤
        ∑' n : ℕ, C_conn * (((n + 1 : ℕ) : ℝ) ^ dim) * A₀ *
          r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊) := by
    exact connectedFiniteSum_le_of_cardBucketBounds_kp_shifted
      (fun Y => (T β F p q).K_bound Y) p q
      r hr_pos hr_lt1 C_conn A₀ hC hA dim
      (fun n hn => cardBucketSum_le_of_count_and_pointwise_shifted
        (fun Y => (T β F p q).K_bound Y) p q
        r hr_pos C_conn A₀ hA dim n
        (h_count p q n hn hdist)
        (fun Y hY => pointwiseBucketBound_of_card_decay
          (fun Y => (T β F p q).K_bound Y) p q r A₀ n Y hY
          (fun Y => h_card_decay β hβ F hF p q Y)))
  rw [TruncatedActivities.connectingBound_eq_finset_sum]
  exact finiteConnectingSum_eq_connectedFiniteSum
    (fun Y => (T β F p q).K_bound Y) p q
    (fun Y hp hq hnot => h_zero β hβ F hF p q Y hp hq hnot) ▸ h_connected

/-- Concrete finite-volume truncated activities whose bound is supported only
on polymers containing `p`, containing `q`, and connected. -/
noncomputable def TruncatedActivities.ofConnectedCardDecay
    {d L : ℕ} [NeZero d] [NeZero L]
    (K : Finset (ConcretePlaquette d L) → ℝ)
    (p q : ConcretePlaquette d L)
    (r A₀ : ℝ) (hr_nonneg : 0 ≤ r) (hA_nonneg : 0 ≤ A₀)
    (hK_abs_le : ∀ Y, |K Y| ≤
      if p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y then A₀ * r ^ Y.card else 0) :
    TruncatedActivities (ConcretePlaquette d L) := by
  classical
  exact TruncatedActivities.ofBound K
    (fun Y =>
      if p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y then A₀ * r ^ Y.card else 0)
    (fun Y => by
      by_cases h : p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y
      · simp [h, mul_nonneg hA_nonneg (pow_nonneg hr_nonneg Y.card)]
      · simp [h])
    hK_abs_le
    (summable_of_hasFiniteSupport (by
      exact Set.finite_univ.subset (by
        intro Y _hY
        exact Set.mem_univ Y)))

/-- The connected-cardinality constructor stores the supplied activity. -/
@[simp] theorem TruncatedActivities.ofConnectedCardDecay_K
    {d L : ℕ} [NeZero d] [NeZero L]
    (K : Finset (ConcretePlaquette d L) → ℝ)
    (p q : ConcretePlaquette d L)
    (r A₀ : ℝ) (hr_nonneg : 0 ≤ r) (hA_nonneg : 0 ≤ A₀)
    (hK_abs_le : ∀ Y, |K Y| ≤
      if p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y then A₀ * r ^ Y.card else 0)
    (Y : Finset (ConcretePlaquette d L)) :
    (TruncatedActivities.ofConnectedCardDecay K p q r A₀
      hr_nonneg hA_nonneg hK_abs_le).K Y = K Y := by
  classical
  rfl

/-- The connected-cardinality constructor's bound is dominated by the global
cardinality-decay profile. -/
theorem TruncatedActivities.ofConnectedCardDecay_K_bound_le_cardDecay
    {d L : ℕ} [NeZero d] [NeZero L]
    (K : Finset (ConcretePlaquette d L) → ℝ)
    (p q : ConcretePlaquette d L)
    (r A₀ : ℝ) (hr_nonneg : 0 ≤ r) (hA_nonneg : 0 ≤ A₀)
    (hK_abs_le : ∀ Y, |K Y| ≤
      if p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y then A₀ * r ^ Y.card else 0)
    (Y : Finset (ConcretePlaquette d L)) :
    (TruncatedActivities.ofConnectedCardDecay K p q r A₀
      hr_nonneg hA_nonneg hK_abs_le).K_bound Y ≤ A₀ * r ^ Y.card := by
  classical
  change (if p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y then A₀ * r ^ Y.card else 0) ≤
    A₀ * r ^ Y.card
  by_cases h : p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y
  · simp [h]
  · simp [h, mul_nonneg hA_nonneg (pow_nonneg hr_nonneg Y.card)]

/-- The connected-cardinality constructor's bound vanishes on disconnected
polymers, even when they contain the two marked plaquettes. -/
theorem TruncatedActivities.ofConnectedCardDecay_K_bound_eq_zero_of_not_connected
    {d L : ℕ} [NeZero d] [NeZero L]
    (K : Finset (ConcretePlaquette d L) → ℝ)
    (p q : ConcretePlaquette d L)
    (r A₀ : ℝ) (hr_nonneg : 0 ≤ r) (hA_nonneg : 0 ≤ A₀)
    (hK_abs_le : ∀ Y, |K Y| ≤
      if p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y then A₀ * r ^ Y.card else 0)
    (Y : Finset (ConcretePlaquette d L))
    (_hp : p ∈ Y) (_hq : q ∈ Y) (h_not_connected : ¬ PolymerConnected Y) :
    (TruncatedActivities.ofConnectedCardDecay K p q r A₀
      hr_nonneg hA_nonneg hK_abs_le).K_bound Y = 0 := by
  classical
  change (if p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y then A₀ * r ^ Y.card else 0) = 0
  have h : ¬ (p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y) := by
    intro hconn
    exact h_not_connected hconn.2.2
  simp [h]

#print axioms finiteConnectingSum_eq_connectedFiniteSum
#print axioms connectedFiniteSum_eq_cardBucketSum
#print axioms connectedFiniteSum_le_of_cardBucketBounds
#print axioms connectedFiniteSum_le_of_cardBucketBounds_shifted
#print axioms connectedFiniteSum_le_of_cardBucketBounds_kp
#print axioms connectedFiniteSum_le_of_cardBucketBounds_kp_shifted
#print axioms cardBucketSum_le_of_count_and_pointwise
#print axioms cardBucketSum_le_of_count_and_pointwise_shifted
#print axioms pointwiseBucketBound_of_card_decay
#print axioms TruncatedActivities.ofConnectedCardDecay
#print axioms TruncatedActivities.ofConnectedCardDecay_K
#print axioms TruncatedActivities.ofConnectedCardDecay_K_bound_le_cardDecay
#print axioms TruncatedActivities.ofConnectedCardDecay_K_bound_eq_zero_of_not_connected
#print axioms clusterCorrelatorBound_of_connectedFiniteBounds_ceil
#print axioms clusterCorrelatorBound_of_cardBucketBounds_ceil
#print axioms clusterCorrelatorBound_of_count_pointwiseBounds_ceil
#print axioms clusterCorrelatorBound_of_count_cardDecayBounds_ceil
#print axioms clusterCorrelatorBound_of_count_cardDecayBounds_ceil_shifted

/-! ### Terminal wrapper from connected finite KP data -/

/-- Terminal F3 wrapper: a Wilson activity bound plus the connected finite
Mayer/KP inputs produce the current Clay theorem endpoint.

This is only a composition theorem. The remaining analytic work is exactly in
`h_mayer`, `h_zero`, and `h_connected_bound`; once those are discharged, this
wrapper feeds the resulting `ClusterCorrelatorBound` into
`clay_theorem_from_wilson_activity`. -/
theorem clay_theorem_of_connectedFiniteBounds_ceil
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ)
    (T : ∀ {d L : ℕ} [NeZero d] [NeZero L],
      (β : ℝ) →
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) →
      ConcretePlaquette d L → ConcretePlaquette d L →
      TruncatedActivities (ConcretePlaquette d L))
    (h_mayer : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q =
      (T β F p q).connectingSum p q)
    (h_zero : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L)
      (Y : Finset (ConcretePlaquette d L)),
      p ∈ Y → q ∈ Y → ¬ PolymerConnected Y →
      (T β F p q).K_bound Y = 0)
    (h_connected_bound : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      (∑ Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
          (fun Y => p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y),
        (T β F p q).K_bound Y) ≤
        ∑' n : ℕ, C_conn * (n : ℝ) ^ dim * A₀ *
          wab.r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊)) :
    ClayYangMillsTheorem := by
  exact clay_theorem_from_wilson_activity wab
    (clusterPrefactor wab.r C_conn A₀ dim)
    (clusterPrefactor_pos wab.r wab.hr_pos wab.hr_lt1 C_conn A₀ hC hA dim)
    (clusterCorrelatorBound_of_connectedFiniteBounds_ceil
      N_c wab.r wab.hr_pos wab.hr_lt1 C_conn A₀ hC hA dim
      T h_mayer h_zero h_connected_bound)

#print axioms clay_theorem_of_connectedFiniteBounds_ceil

/-- Terminal wrapper from cardinal-bucket KP estimates. This is the endpoint
composition whose only F3 analytic estimate is the bucket bound itself. -/
theorem clay_theorem_of_cardBucketBounds_ceil
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ)
    (T : ∀ {d L : ℕ} [NeZero d] [NeZero L],
      (β : ℝ) →
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) →
      ConcretePlaquette d L → ConcretePlaquette d L →
      TruncatedActivities (ConcretePlaquette d L))
    (h_mayer : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q =
      (T β F p q).connectingSum p q)
    (h_zero : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L)
      (Y : Finset (ConcretePlaquette d L)),
      p ∈ Y → q ∈ Y → ¬ PolymerConnected Y →
      (T β F p q).K_bound Y = 0)
    (h_bucket : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L)
      (n : ℕ),
      n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1) →
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      (∑ Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
          (fun Y => p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y),
          if Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊
            then (T β F p q).K_bound Y else 0) ≤
        C_conn * (n : ℝ) ^ dim * A₀ *
          wab.r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊)) :
    ClayYangMillsTheorem := by
  exact clay_theorem_from_wilson_activity wab
    (clusterPrefactor wab.r C_conn A₀ dim)
    (clusterPrefactor_pos wab.r wab.hr_pos wab.hr_lt1 C_conn A₀ hC hA dim)
    (clusterCorrelatorBound_of_cardBucketBounds_ceil
      N_c wab.r wab.hr_pos wab.hr_lt1 C_conn A₀ hC hA dim
      T h_mayer h_zero h_bucket)

#print axioms clay_theorem_of_cardBucketBounds_ceil

/-- Terminal wrapper from bucket cardinality and pointwise activity bounds.

This is the most factored F3 endpoint: the remaining analytic inputs are the
Mayer identity, disconnected support cancellation, the lattice-animal bucket
count, and the pointwise polymer activity bound. -/
theorem clay_theorem_of_count_pointwiseBounds_ceil
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ)
    (T : ∀ {d L : ℕ} [NeZero d] [NeZero L],
      (β : ℝ) →
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) →
      ConcretePlaquette d L → ConcretePlaquette d L →
      TruncatedActivities (ConcretePlaquette d L))
    (h_mayer : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q =
      (T β F p q).connectingSum p q)
    (h_zero : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L)
      (Y : Finset (ConcretePlaquette d L)),
      p ∈ Y → q ∈ Y → ¬ PolymerConnected Y →
      (T β F p q).K_bound Y = 0)
    (h_count : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (p q : ConcretePlaquette d L) (n : ℕ),
      n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1) →
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun Y =>
          p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y ∧
            Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
        C_conn * (n : ℝ) ^ dim)
    (h_pointwise : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L)
      (n : ℕ)
      (Y : Finset (ConcretePlaquette d L)),
      n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1) →
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      Y ∈ (Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun Y =>
          p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y ∧
            Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊) →
      (T β F p q).K_bound Y ≤
        A₀ * wab.r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊)) :
    ClayYangMillsTheorem := by
  exact clay_theorem_from_wilson_activity wab
    (clusterPrefactor wab.r C_conn A₀ dim)
    (clusterPrefactor_pos wab.r wab.hr_pos wab.hr_lt1 C_conn A₀ hC hA dim)
    (clusterCorrelatorBound_of_count_pointwiseBounds_ceil
      N_c wab.r wab.hr_pos wab.hr_lt1 C_conn A₀ hC hA dim
      T h_mayer h_zero h_count h_pointwise)

#print axioms clay_theorem_of_count_pointwiseBounds_ceil

/-- Terminal wrapper from bucket cardinality plus global cardinality-decay of
the truncated activity bound.  This packages the pointwise bucket estimate
through `pointwiseBucketBound_of_card_decay`. -/
theorem clay_theorem_of_count_cardDecayBounds_ceil
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ)
    (T : ∀ {d L : ℕ} [NeZero d] [NeZero L],
      (β : ℝ) →
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) →
      ConcretePlaquette d L → ConcretePlaquette d L →
      TruncatedActivities (ConcretePlaquette d L))
    (h_mayer : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q =
      (T β F p q).connectingSum p q)
    (h_zero : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L)
      (Y : Finset (ConcretePlaquette d L)),
      p ∈ Y → q ∈ Y → ¬ PolymerConnected Y →
      (T β F p q).K_bound Y = 0)
    (h_count : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (p q : ConcretePlaquette d L) (n : ℕ),
      n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1) →
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun Y =>
          p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y ∧
            Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
        C_conn * (n : ℝ) ^ dim)
    (h_card_decay : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L)
      (Y : Finset (ConcretePlaquette d L)),
      (T β F p q).K_bound Y ≤ A₀ * wab.r ^ Y.card) :
    ClayYangMillsTheorem := by
  exact clay_theorem_from_wilson_activity wab
    (clusterPrefactor wab.r C_conn A₀ dim)
    (clusterPrefactor_pos wab.r wab.hr_pos wab.hr_lt1 C_conn A₀ hC hA dim)
    (clusterCorrelatorBound_of_count_cardDecayBounds_ceil
      N_c wab.r wab.hr_pos wab.hr_lt1 C_conn A₀ hC hA dim
      T h_mayer h_zero h_count h_card_decay)

#print axioms clay_theorem_of_count_cardDecayBounds_ceil

/-- Terminal wrapper from raw connected-cardinality-decay truncated
activities.  The disconnected support cancellation and global `K_bound`
decay are supplied by `TruncatedActivities.ofConnectedCardDecay`; the remaining
F3 inputs are the Mayer identity, the connected pointwise activity bound, and
the lattice-animal bucket count. -/
theorem clay_theorem_of_count_connectedCardDecayActivities_ceil
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ)
    (K : ∀ {d L : ℕ} [NeZero d] [NeZero L],
      (β : ℝ) →
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) →
      ConcretePlaquette d L → ConcretePlaquette d L →
      Finset (ConcretePlaquette d L) → ℝ)
    (hK_abs_le : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (p q : ConcretePlaquette d L)
      (Y : Finset (ConcretePlaquette d L)),
      |K β F p q Y| ≤
        if p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y
          then A₀ * wab.r ^ Y.card else 0)
    (h_mayer : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q =
      (TruncatedActivities.ofConnectedCardDecay
        (K β F p q) p q wab.r A₀ wab.hr_pos.le hA.le
        (hK_abs_le β F p q)).connectingSum p q)
    (h_count : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (p q : ConcretePlaquette d L) (n : ℕ),
      n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1) →
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun Y =>
          p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y ∧
            Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
        C_conn * (n : ℝ) ^ dim) :
    ClayYangMillsTheorem := by
  let T : ∀ {d L : ℕ} [NeZero d] [NeZero L],
      (β : ℝ) →
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) →
      ConcretePlaquette d L → ConcretePlaquette d L →
      TruncatedActivities (ConcretePlaquette d L) :=
    fun {d L} [NeZero d] [NeZero L] β F p q =>
      TruncatedActivities.ofConnectedCardDecay
        (K β F p q) p q wab.r A₀ wab.hr_pos.le hA.le
        (hK_abs_le β F p q)
  refine clay_theorem_of_count_cardDecayBounds_ceil
    N_c wab C_conn A₀ hC hA dim T ?_ ?_ h_count ?_
  · intro d L _ _ β hβ F hF p q hdist
    exact h_mayer β hβ F hF p q hdist
  · intro d L _ _ β hβ F hF p q Y hp hq h_not_connected
    exact TruncatedActivities.ofConnectedCardDecay_K_bound_eq_zero_of_not_connected
      (K β F p q) p q wab.r A₀ wab.hr_pos.le hA.le
      (hK_abs_le β F p q) Y hp hq h_not_connected
  · intro d L _ _ β _hβ F _hF p q Y
    exact TruncatedActivities.ofConnectedCardDecay_K_bound_le_cardDecay
      (K β F p q) p q wab.r A₀ wab.hr_pos.le hA.le
      (hK_abs_le β F p q) Y

#print axioms clay_theorem_of_count_connectedCardDecayActivities_ceil

/-- Shifted terminal wrapper from raw connected-cardinality-decay truncated
activities.  This is the same endpoint as
`clay_theorem_of_count_connectedCardDecayActivities_ceil`, but consumes the
natural bucket count `C_conn * (n+1)^dim` and uses
`clusterPrefactorShifted`. -/
theorem clay_theorem_of_count_connectedCardDecayActivities_ceil_shifted
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ)
    (K : ∀ {d L : ℕ} [NeZero d] [NeZero L],
      (β : ℝ) →
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) →
      ConcretePlaquette d L → ConcretePlaquette d L →
      Finset (ConcretePlaquette d L) → ℝ)
    (hK_abs_le : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (p q : ConcretePlaquette d L)
      (Y : Finset (ConcretePlaquette d L)),
      |K β F p q Y| ≤
        if p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y
          then A₀ * wab.r ^ Y.card else 0)
    (h_mayer : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q =
      (TruncatedActivities.ofConnectedCardDecay
        (K β F p q) p q wab.r A₀ wab.hr_pos.le hA.le
        (hK_abs_le β F p q)).connectingSum p q)
    (h_count : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (p q : ConcretePlaquette d L) (n : ℕ),
      n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1) →
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
        (fun Y =>
          p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y ∧
            Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
        C_conn * (((n + 1 : ℕ) : ℝ) ^ dim)) :
    ClayYangMillsTheorem := by
  let T : ∀ {d L : ℕ} [NeZero d] [NeZero L],
      (β : ℝ) →
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) →
      ConcretePlaquette d L → ConcretePlaquette d L →
      TruncatedActivities (ConcretePlaquette d L) :=
    fun {d L} [NeZero d] [NeZero L] β F p q =>
      TruncatedActivities.ofConnectedCardDecay
        (K β F p q) p q wab.r A₀ wab.hr_pos.le hA.le
        (hK_abs_le β F p q)
  exact clay_theorem_from_wilson_activity wab
    (clusterPrefactorShifted wab.r C_conn A₀ dim)
    (clusterPrefactorShifted_pos wab.r wab.hr_pos wab.hr_lt1 C_conn A₀ hC hA dim)
    (clusterCorrelatorBound_of_count_cardDecayBounds_ceil_shifted
      N_c wab.r wab.hr_pos wab.hr_lt1 C_conn A₀ hC hA dim
      T
      (by
        intro d L _ _ β hβ F hF p q hdist
        exact h_mayer β hβ F hF p q hdist)
      (by
        intro d L _ _ β hβ F hF p q Y hp hq h_not_connected
        exact TruncatedActivities.ofConnectedCardDecay_K_bound_eq_zero_of_not_connected
          (K β F p q) p q wab.r A₀ wab.hr_pos.le hA.le
          (hK_abs_le β F p q) Y hp hq h_not_connected)
      h_count
      (by
        intro d L _ _ β _hβ F _hF p q Y
        exact TruncatedActivities.ofConnectedCardDecay_K_bound_le_cardDecay
          (K β F p q) p q wab.r A₀ wab.hr_pos.le hA.le
          (hK_abs_le β F p q) Y))

#print axioms clay_theorem_of_count_connectedCardDecayActivities_ceil_shifted

/-- A packaged raw truncated-activity input for the preferred shifted F3
endpoint.

It contains the raw truncated activity `K`, its connected-cardinality decay
bound, and the Mayer/Ursell identity identifying the Wilson connected
correlator with the connecting sum of the constructed activity. -/
structure ConnectedCardDecayMayerData
    (N_c : ℕ) [NeZero N_c]
    (r A₀ : ℝ) (hr_nonneg : 0 ≤ r) (hA_nonneg : 0 ≤ A₀) where
  K : ∀ {d L : ℕ} [NeZero d] [NeZero L],
    (β : ℝ) →
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) →
    ConcretePlaquette d L → ConcretePlaquette d L →
    Finset (ConcretePlaquette d L) → ℝ
  hK_abs_le : ∀ {d L : ℕ} [NeZero d] [NeZero L]
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (p q : ConcretePlaquette d L)
    (Y : Finset (ConcretePlaquette d L)),
    |K β F p q Y| ≤
      if p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y
        then A₀ * r ^ Y.card else 0
  h_mayer : ∀ {d L : ℕ} [NeZero d] [NeZero L]
    (β : ℝ) (_hβ : 0 < β)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (_hF : ∀ U, |F U| ≤ 1)
    (p q : ConcretePlaquette d L),
    (1 : ℝ) ≤ siteLatticeDist p.site q.site →
    wilsonConnectedCorr (sunHaarProb N_c)
      (wilsonPlaquetteEnergy N_c) β F p q =
    (TruncatedActivities.ofConnectedCardDecay
      (K β F p q) p q r A₀ hr_nonneg hA_nonneg
      (hK_abs_le β F p q)).connectingSum p q

namespace ConnectedCardDecayMayerData

/-- Convert packaged Mayer/activity data into the finite-volume truncated
activities used by the shifted F3 counting wrappers. -/
noncomputable def toTruncatedActivities
    {N_c : ℕ} [NeZero N_c]
    {r A₀ : ℝ} {hr_nonneg : 0 ≤ r} {hA_nonneg : 0 ≤ A₀}
    (data : ConnectedCardDecayMayerData N_c r A₀ hr_nonneg hA_nonneg)
    {d L : ℕ} [NeZero d] [NeZero L]
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (p q : ConcretePlaquette d L) :
    TruncatedActivities (ConcretePlaquette d L) :=
  TruncatedActivities.ofConnectedCardDecay
    (data.K β F p q) p q r A₀ hr_nonneg hA_nonneg
    (data.hK_abs_le β F p q)

/-- The activity projection of `toTruncatedActivities` is the packaged raw
Mayer activity. -/
@[simp] theorem toTruncatedActivities_K
    {N_c : ℕ} [NeZero N_c]
    {r A₀ : ℝ} {hr_nonneg : 0 ≤ r} {hA_nonneg : 0 ≤ A₀}
    (data : ConnectedCardDecayMayerData N_c r A₀ hr_nonneg hA_nonneg)
    {d L : ℕ} [NeZero d] [NeZero L]
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (p q : ConcretePlaquette d L)
    (Y : Finset (ConcretePlaquette d L)) :
    (data.toTruncatedActivities β F p q).K Y = data.K β F p q Y := by
  rfl

/-- The connected-cardinality bound supplied by `toTruncatedActivities` is
dominated by the package's global cardinality-decay profile. -/
theorem toTruncatedActivities_K_bound_le_cardDecay
    {N_c : ℕ} [NeZero N_c]
    {r A₀ : ℝ} {hr_nonneg : 0 ≤ r} {hA_nonneg : 0 ≤ A₀}
    (data : ConnectedCardDecayMayerData N_c r A₀ hr_nonneg hA_nonneg)
    {d L : ℕ} [NeZero d] [NeZero L]
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (p q : ConcretePlaquette d L)
    (Y : Finset (ConcretePlaquette d L)) :
    (data.toTruncatedActivities β F p q).K_bound Y ≤ A₀ * r ^ Y.card := by
  exact TruncatedActivities.ofConnectedCardDecay_K_bound_le_cardDecay
    (data.K β F p q) p q r A₀ hr_nonneg hA_nonneg
    (data.hK_abs_le β F p q) Y

/-- The bound supplied by `toTruncatedActivities` vanishes on disconnected
polymers, even when they contain the two marked plaquettes. -/
theorem toTruncatedActivities_K_bound_eq_zero_of_not_connected
    {N_c : ℕ} [NeZero N_c]
    {r A₀ : ℝ} {hr_nonneg : 0 ≤ r} {hA_nonneg : 0 ≤ A₀}
    (data : ConnectedCardDecayMayerData N_c r A₀ hr_nonneg hA_nonneg)
    {d L : ℕ} [NeZero d] [NeZero L]
    (β : ℝ)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (p q : ConcretePlaquette d L)
    (Y : Finset (ConcretePlaquette d L))
    (hp : p ∈ Y) (hq : q ∈ Y) (h_not_connected : ¬ PolymerConnected Y) :
    (data.toTruncatedActivities β F p q).K_bound Y = 0 := by
  exact TruncatedActivities.ofConnectedCardDecay_K_bound_eq_zero_of_not_connected
    (data.K β F p q) p q r A₀ hr_nonneg hA_nonneg
    (data.hK_abs_le β F p q) Y hp hq h_not_connected

/-- The packaged Mayer/Ursell identity, restated through
`toTruncatedActivities`. -/
theorem wilsonConnectedCorr_eq_toTruncatedActivities_connectingSum
    {N_c : ℕ} [NeZero N_c]
    {r A₀ : ℝ} {hr_nonneg : 0 ≤ r} {hA_nonneg : 0 ≤ A₀}
    (data : ConnectedCardDecayMayerData N_c r A₀ hr_nonneg hA_nonneg)
    {d L : ℕ} [NeZero d] [NeZero L]
    (β : ℝ) (hβ : 0 < β)
    (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
    (hF : ∀ U, |F U| ≤ 1)
    (p q : ConcretePlaquette d L)
    (hdist : (1 : ℝ) ≤ siteLatticeDist p.site q.site) :
    wilsonConnectedCorr (sunHaarProb N_c)
      (wilsonPlaquetteEnergy N_c) β F p q =
    (data.toTruncatedActivities β F p q).connectingSum p q := by
  exact data.h_mayer β hβ F hF p q hdist

end ConnectedCardDecayMayerData

#print axioms ConnectedCardDecayMayerData.toTruncatedActivities
#print axioms ConnectedCardDecayMayerData.toTruncatedActivities_K
#print axioms ConnectedCardDecayMayerData.toTruncatedActivities_K_bound_le_cardDecay
#print axioms ConnectedCardDecayMayerData.toTruncatedActivities_K_bound_eq_zero_of_not_connected
#print axioms ConnectedCardDecayMayerData.wilsonConnectedCorr_eq_toTruncatedActivities_connectingSum

/-- Preferred terminal F3 wrapper with the shifted bucket count packaged as the
named frontier predicate `ShiftedConnectingClusterCountBound`. -/
theorem clay_theorem_of_shiftedCountBound_connectedCardDecayActivities_ceil
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ)
    (K : ∀ {d L : ℕ} [NeZero d] [NeZero L],
      (β : ℝ) →
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) →
      ConcretePlaquette d L → ConcretePlaquette d L →
      Finset (ConcretePlaquette d L) → ℝ)
    (hK_abs_le : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (p q : ConcretePlaquette d L)
      (Y : Finset (ConcretePlaquette d L)),
      |K β F p q Y| ≤
        if p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y
          then A₀ * wab.r ^ Y.card else 0)
    (h_mayer : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q =
      (TruncatedActivities.ofConnectedCardDecay
        (K β F p q) p q wab.r A₀ wab.hr_pos.le hA.le
        (hK_abs_le β F p q)).connectingSum p q)
    (h_count : ShiftedConnectingClusterCountBound C_conn dim) :
    ClayYangMillsTheorem :=
  clay_theorem_of_count_connectedCardDecayActivities_ceil_shifted
    N_c wab C_conn A₀ hC hA dim K hK_abs_le h_mayer
    (fun p q n hn hdist =>
      h_count.apply p q n hn hdist)

#print axioms clay_theorem_of_shiftedCountBound_connectedCardDecayActivities_ceil

/-- Preferred terminal F3 wrapper with both remaining analytic sides packaged:
`ConnectedCardDecayMayerData` for the raw Mayer/activity input and
`ShiftedConnectingClusterCountBound` for the lattice-animal count. -/
theorem clusterCorrelatorBound_of_shiftedCountBound_mayerData_ceil
    (N_c : ℕ) [NeZero N_c]
    (r : ℝ) (hr_pos : 0 < r) (hr_lt1 : r < 1)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ)
    (data : ConnectedCardDecayMayerData N_c r A₀ hr_pos.le hA.le)
    (h_count : ShiftedConnectingClusterCountBound C_conn dim) :
    ClusterCorrelatorBound N_c r
      (clusterPrefactorShifted r C_conn A₀ dim) := by
  exact clusterCorrelatorBound_of_count_cardDecayBounds_ceil_shifted
    (N_c := N_c) (r := r) (hr_pos := hr_pos) (hr_lt1 := hr_lt1)
    (C_conn := C_conn) (A₀ := A₀) (hC := hC) (hA := hA)
    (dim := dim)
    (T := fun {d L} [NeZero d] [NeZero L] β F p q =>
      data.toTruncatedActivities β F p q)
    (by
      intro d L _ _ β hβ F hF p q hdist
      exact data.wilsonConnectedCorr_eq_toTruncatedActivities_connectingSum
        β hβ F hF p q hdist)
    (by
      intro d L _ _ β _hβ F _hF p q Y hp hq h_not_connected
      exact data.toTruncatedActivities_K_bound_eq_zero_of_not_connected
        β F p q Y hp hq h_not_connected)
    (fun p q n hn hdist => h_count.apply p q n hn hdist)
    (by
      intro d L _ _ β _hβ F _hF p q Y
      exact data.toTruncatedActivities_K_bound_le_cardDecay β F p q Y)

#print axioms clusterCorrelatorBound_of_shiftedCountBound_mayerData_ceil

/-- Preferred F3 endpoint into the older analytic witness bundle. -/
noncomputable def clayWitnessHyp_of_shiftedCountBound_mayerData_ceil
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ)
    (data : ConnectedCardDecayMayerData N_c wab.r A₀ wab.hr_pos.le hA.le)
    (h_count : ShiftedConnectingClusterCountBound C_conn dim) :
    ClayWitnessHyp N_c :=
  clayWitnessHyp_of_clusterCorrelatorBound N_c
    wab.r wab.hr_pos wab.hr_lt1
    (clusterPrefactorShifted wab.r C_conn A₀ dim)
    (clusterPrefactorShifted_pos wab.r wab.hr_pos wab.hr_lt1 C_conn A₀ hC hA dim)
    (clusterCorrelatorBound_of_shiftedCountBound_mayerData_ceil
      N_c wab.r wab.hr_pos wab.hr_lt1 C_conn A₀ hC hA dim data h_count)

#print axioms clayWitnessHyp_of_shiftedCountBound_mayerData_ceil

/-- Authentic Clay-facing F3 wrapper: the preferred shifted Mayer/count packages
produce the non-vacuous mass-gap structure, not merely the weak existential
`ClayYangMillsTheorem`. -/
noncomputable def clayMassGap_of_shiftedCountBound_mayerData_ceil
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ)
    (data : ConnectedCardDecayMayerData N_c wab.r A₀ wab.hr_pos.le hA.le)
    (h_count : ShiftedConnectingClusterCountBound C_conn dim) :
    ClayYangMillsMassGap N_c :=
  clay_massGap_large_beta N_c wab.r wab.hr_pos wab.hr_lt1
    (clusterPrefactorShifted wab.r C_conn A₀ dim)
    (clusterPrefactorShifted_pos wab.r wab.hr_pos wab.hr_lt1 C_conn A₀ hC hA dim)
    (clusterCorrelatorBound_of_shiftedCountBound_mayerData_ceil
      N_c wab.r wab.hr_pos wab.hr_lt1 C_conn A₀ hC hA dim data h_count)

#print axioms clayMassGap_of_shiftedCountBound_mayerData_ceil

/-- Preferred F3 endpoint into the connected-correlator-decay hub. -/
noncomputable def clayConnectedCorrDecay_of_shiftedCountBound_mayerData_ceil
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ)
    (data : ConnectedCardDecayMayerData N_c wab.r A₀ wab.hr_pos.le hA.le)
    (h_count : ShiftedConnectingClusterCountBound C_conn dim) :
    ClayConnectedCorrDecay N_c :=
  ClayConnectedCorrDecay.ofClayMassGap
    (clayMassGap_of_shiftedCountBound_mayerData_ceil
      N_c wab C_conn A₀ hC hA dim data h_count)

#print axioms clayConnectedCorrDecay_of_shiftedCountBound_mayerData_ceil

/-- Authentic Clay-facing F3 wrapper with the Mayer/activity package supplied
as separate fields rather than as `ConnectedCardDecayMayerData`. -/
noncomputable def clayMassGap_of_shiftedCountBound_connectedCardDecayActivities_ceil
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ)
    (K : ∀ {d L : ℕ} [NeZero d] [NeZero L],
      (β : ℝ) →
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) →
      ConcretePlaquette d L → ConcretePlaquette d L →
      Finset (ConcretePlaquette d L) → ℝ)
    (hK_abs_le : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (p q : ConcretePlaquette d L)
      (Y : Finset (ConcretePlaquette d L)),
      |K β F p q Y| ≤
        if p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y
          then A₀ * wab.r ^ Y.card else 0)
    (h_mayer : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q =
      (TruncatedActivities.ofConnectedCardDecay
        (K β F p q) p q wab.r A₀ wab.hr_pos.le hA.le
        (hK_abs_le β F p q)).connectingSum p q)
    (h_count : ShiftedConnectingClusterCountBound C_conn dim) :
    ClayYangMillsMassGap N_c :=
  clayMassGap_of_shiftedCountBound_mayerData_ceil
    N_c wab C_conn A₀ hC hA dim
    ({ K := K, hK_abs_le := hK_abs_le, h_mayer := h_mayer } :
      ConnectedCardDecayMayerData N_c wab.r A₀ wab.hr_pos.le hA.le)
    h_count

#print axioms clayMassGap_of_shiftedCountBound_connectedCardDecayActivities_ceil

/-- Unpackaged F3 endpoint into the older analytic witness bundle. -/
noncomputable def clayWitnessHyp_of_shiftedCountBound_connectedCardDecayActivities_ceil
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ)
    (K : ∀ {d L : ℕ} [NeZero d] [NeZero L],
      (β : ℝ) →
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) →
      ConcretePlaquette d L → ConcretePlaquette d L →
      Finset (ConcretePlaquette d L) → ℝ)
    (hK_abs_le : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (p q : ConcretePlaquette d L)
      (Y : Finset (ConcretePlaquette d L)),
      |K β F p q Y| ≤
        if p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y
          then A₀ * wab.r ^ Y.card else 0)
    (h_mayer : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q =
      (TruncatedActivities.ofConnectedCardDecay
        (K β F p q) p q wab.r A₀ wab.hr_pos.le hA.le
        (hK_abs_le β F p q)).connectingSum p q)
    (h_count : ShiftedConnectingClusterCountBound C_conn dim) :
    ClayWitnessHyp N_c :=
  clayWitnessHyp_of_shiftedCountBound_mayerData_ceil
    N_c wab C_conn A₀ hC hA dim
    ({ K := K, hK_abs_le := hK_abs_le, h_mayer := h_mayer } :
      ConnectedCardDecayMayerData N_c wab.r A₀ wab.hr_pos.le hA.le)
    h_count

#print axioms clayWitnessHyp_of_shiftedCountBound_connectedCardDecayActivities_ceil

/-- Unpackaged F3 endpoint into the connected-correlator-decay hub. -/
noncomputable def clayConnectedCorrDecay_of_shiftedCountBound_connectedCardDecayActivities_ceil
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ)
    (K : ∀ {d L : ℕ} [NeZero d] [NeZero L],
      (β : ℝ) →
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ) →
      ConcretePlaquette d L → ConcretePlaquette d L →
      Finset (ConcretePlaquette d L) → ℝ)
    (hK_abs_le : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (p q : ConcretePlaquette d L)
      (Y : Finset (ConcretePlaquette d L)),
      |K β F p q Y| ≤
        if p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y
          then A₀ * wab.r ^ Y.card else 0)
    (h_mayer : ∀ {d L : ℕ} [NeZero d] [NeZero L]
      (β : ℝ) (_hβ : 0 < β)
      (F : ↑(Matrix.specialUnitaryGroup (Fin N_c) ℂ) → ℝ)
      (_hF : ∀ U, |F U| ≤ 1)
      (p q : ConcretePlaquette d L),
      (1 : ℝ) ≤ siteLatticeDist p.site q.site →
      wilsonConnectedCorr (sunHaarProb N_c)
        (wilsonPlaquetteEnergy N_c) β F p q =
      (TruncatedActivities.ofConnectedCardDecay
        (K β F p q) p q wab.r A₀ wab.hr_pos.le hA.le
        (hK_abs_le β F p q)).connectingSum p q)
    (h_count : ShiftedConnectingClusterCountBound C_conn dim) :
    ClayConnectedCorrDecay N_c :=
  ClayConnectedCorrDecay.ofClayMassGap
    (clayMassGap_of_shiftedCountBound_connectedCardDecayActivities_ceil
      N_c wab C_conn A₀ hC hA dim K hK_abs_le h_mayer h_count)

#print axioms clayConnectedCorrDecay_of_shiftedCountBound_connectedCardDecayActivities_ceil

/-- Preferred terminal F3 wrapper with both remaining analytic sides packaged:
`ConnectedCardDecayMayerData` for the raw Mayer/activity input and
`ShiftedConnectingClusterCountBound` for the lattice-animal count. -/
theorem clay_theorem_of_shiftedCountBound_mayerData_ceil
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
    (dim : ℕ)
    (data : ConnectedCardDecayMayerData N_c wab.r A₀ wab.hr_pos.le hA.le)
    (h_count : ShiftedConnectingClusterCountBound C_conn dim) :
    ClayYangMillsTheorem :=
  clayMassGap_implies_clayTheorem
    (clayMassGap_of_shiftedCountBound_mayerData_ceil
      N_c wab C_conn A₀ hC hA dim data h_count)

#print axioms clay_theorem_of_shiftedCountBound_mayerData_ceil

/-! ### Single-package preferred F3 interface -/

/-- Mayer/activity half of the preferred shifted F3 frontier. -/
structure ShiftedF3MayerPackage
    (N_c : ℕ) [NeZero N_c] (wab : WilsonPolymerActivityBound N_c) where
  A₀ : ℝ
  hA : 0 < A₀
  data : ConnectedCardDecayMayerData N_c wab.r A₀ wab.hr_pos.le hA.le

/-- SU(1) canary for the shifted F3 Mayer interface.

Since the SU(1) connected Wilson correlator vanishes identically, the raw
truncated activity can be the zero activity.  This is not the `N_c ≥ 2`
Mayer/Ursell construction; it records that the preferred F3 package interface
correctly accepts the already-closed singleton case. -/
noncomputable def shiftedF3MayerPackage_su1_zero
    (wab : WilsonPolymerActivityBound 1) :
    ShiftedF3MayerPackage 1 wab where
  A₀ := 1
  hA := one_pos
  data :=
    { K := fun _β _F _p _q _Y => 0
      hK_abs_le := by
        intro d L _ _ β F p q Y
        by_cases h : p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y
        · simp [h, wab.hr_pos.le]
        · simp [h]
      h_mayer := by
        intro d L _ _ β _hβ F _hF p q _hdist
        rw [wilsonConnectedCorr_su1_eq_zero]
        have hsum :
            (TruncatedActivities.ofConnectedCardDecay
              (fun _Y : Finset (ConcretePlaquette d L) => 0)
              p q wab.r 1 wab.hr_pos.le zero_le_one
              (by
                intro Y
                by_cases h : p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y
                · simp [h, wab.hr_pos.le]
                · simp [h])).connectingSum p q = 0 := by
          unfold TruncatedActivities.connectingSum
          have hfun :
              (fun Y : Finset (ConcretePlaquette d L) =>
                if p ∈ Y ∧ q ∈ Y then
                  (TruncatedActivities.ofConnectedCardDecay
                    (fun _Y : Finset (ConcretePlaquette d L) => 0)
                    p q wab.r 1 wab.hr_pos.le zero_le_one
                    (by
                      intro Y
                      by_cases h : p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y
                      · simp [h, wab.hr_pos.le]
                      · simp [h])).K Y
                else 0) = fun _ => 0 := by
            funext Y
            by_cases h : p ∈ Y ∧ q ∈ Y
            · simp [h, TruncatedActivities.ofConnectedCardDecay,
                TruncatedActivities.ofBound]
            · simp [h]
          rw [hfun, tsum_zero]
        simpa using hsum.symm }

/-- Count half of the preferred shifted F3 frontier. -/
structure ShiftedF3CountPackage where
  C_conn : ℝ
  hC : 0 < C_conn
  dim : ℕ
  h_count : ShiftedConnectingClusterCountBound C_conn dim

namespace ShiftedF3CountPackage

/-- Restrict a global shifted F3 count package to a fixed finite plaquette
lattice. -/
def toAt
    (pkg : ShiftedF3CountPackage)
    (d L : ℕ) [NeZero d] [NeZero L] :
    ShiftedF3CountPackageAt d L where
  C_conn := pkg.C_conn
  hC := pkg.hC
  dim := pkg.dim
  h_count := ShiftedConnectingClusterCountBound.toAt pkg.h_count d L

@[simp] theorem toAt_C_conn
    (pkg : ShiftedF3CountPackage)
    (d L : ℕ) [NeZero d] [NeZero L] :
    (pkg.toAt d L).C_conn = pkg.C_conn := rfl

@[simp] theorem toAt_dim
    (pkg : ShiftedF3CountPackage)
    (d L : ℕ) [NeZero d] [NeZero L] :
    (pkg.toAt d L).dim = pkg.dim := rfl

/-- Applying a global shifted F3 count package after restriction to a finite
plaquette lattice is definitionally the global shifted count bound specialized
to that lattice. -/
theorem toAt_apply
    (pkg : ShiftedF3CountPackage)
    (d L : ℕ) [NeZero d] [NeZero L]
    (p q : ConcretePlaquette d L) (n : ℕ)
    (hn : n ∈ Finset.range (Fintype.card (ConcretePlaquette d L) + 1))
    (hdist : (1 : ℝ) ≤ siteLatticeDist p.site q.site) :
    (((Finset.univ : Finset (Finset (ConcretePlaquette d L))).filter
      (fun X =>
        p ∈ X ∧ q ∈ X ∧ PolymerConnected X ∧
          X.card = n + ⌈siteLatticeDist p.site q.site⌉₊)).card : ℝ) ≤
      (pkg.toAt d L).C_conn *
        (((n + 1 : ℕ) : ℝ) ^ (pkg.toAt d L).dim) :=
  (pkg.toAt d L).h_count.apply p q n hn hdist

end ShiftedF3CountPackage

/-- Single preferred package for the shifted F3 route.

It gathers the constants, Mayer/activity data, and shifted lattice-animal count
into one object.  Supplying this package is exactly the remaining preferred F3
frontier. -/
structure ShiftedF3MayerCountPackage
    (N_c : ℕ) [NeZero N_c] (wab : WilsonPolymerActivityBound N_c) where
  C_conn : ℝ
  A₀ : ℝ
  hC : 0 < C_conn
  hA : 0 < A₀
  dim : ℕ
  data : ConnectedCardDecayMayerData N_c wab.r A₀ wab.hr_pos.le hA.le
  h_count : ShiftedConnectingClusterCountBound C_conn dim

namespace ShiftedF3MayerCountPackage

/-- Combine independently-produced Mayer/activity and count packages into the
single preferred F3 frontier object. -/
def ofSubpackages
    {N_c : ℕ} [NeZero N_c] {wab : WilsonPolymerActivityBound N_c}
    (mayer : ShiftedF3MayerPackage N_c wab)
    (count : ShiftedF3CountPackage) :
    ShiftedF3MayerCountPackage N_c wab where
  C_conn := count.C_conn
  A₀ := mayer.A₀
  hC := count.hC
  hA := mayer.hA
  dim := count.dim
  data := mayer.data
  h_count := count.h_count

/-- Project the Mayer/activity half out of a single preferred F3 package. -/
def mayerPackage
    {N_c : ℕ} [NeZero N_c] {wab : WilsonPolymerActivityBound N_c}
    (pkg : ShiftedF3MayerCountPackage N_c wab) :
    ShiftedF3MayerPackage N_c wab where
  A₀ := pkg.A₀
  hA := pkg.hA
  data := pkg.data

/-- Project the count half out of a single preferred F3 package. -/
def countPackage
    {N_c : ℕ} [NeZero N_c] {wab : WilsonPolymerActivityBound N_c}
    (pkg : ShiftedF3MayerCountPackage N_c wab) :
    ShiftedF3CountPackage where
  C_conn := pkg.C_conn
  hC := pkg.hC
  dim := pkg.dim
  h_count := pkg.h_count

@[simp] theorem ofSubpackages_C_conn
    {N_c : ℕ} [NeZero N_c] {wab : WilsonPolymerActivityBound N_c}
    (mayer : ShiftedF3MayerPackage N_c wab)
    (count : ShiftedF3CountPackage) :
    (ofSubpackages mayer count).C_conn = count.C_conn := rfl

@[simp] theorem ofSubpackages_A₀
    {N_c : ℕ} [NeZero N_c] {wab : WilsonPolymerActivityBound N_c}
    (mayer : ShiftedF3MayerPackage N_c wab)
    (count : ShiftedF3CountPackage) :
    (ofSubpackages mayer count).A₀ = mayer.A₀ := rfl

@[simp] theorem ofSubpackages_dim
    {N_c : ℕ} [NeZero N_c] {wab : WilsonPolymerActivityBound N_c}
    (mayer : ShiftedF3MayerPackage N_c wab)
    (count : ShiftedF3CountPackage) :
    (ofSubpackages mayer count).dim = count.dim := rfl

@[simp] theorem ofSubpackages_data
    {N_c : ℕ} [NeZero N_c] {wab : WilsonPolymerActivityBound N_c}
    (mayer : ShiftedF3MayerPackage N_c wab)
    (count : ShiftedF3CountPackage) :
    (ofSubpackages mayer count).data = mayer.data := rfl

@[simp] theorem mayerPackage_A₀
    {N_c : ℕ} [NeZero N_c] {wab : WilsonPolymerActivityBound N_c}
    (pkg : ShiftedF3MayerCountPackage N_c wab) :
    (mayerPackage pkg).A₀ = pkg.A₀ := rfl

@[simp] theorem mayerPackage_data
    {N_c : ℕ} [NeZero N_c] {wab : WilsonPolymerActivityBound N_c}
    (pkg : ShiftedF3MayerCountPackage N_c wab) :
    (mayerPackage pkg).data = pkg.data := rfl

@[simp] theorem countPackage_C_conn
    {N_c : ℕ} [NeZero N_c] {wab : WilsonPolymerActivityBound N_c}
    (pkg : ShiftedF3MayerCountPackage N_c wab) :
    (countPackage pkg).C_conn = pkg.C_conn := rfl

@[simp] theorem countPackage_dim
    {N_c : ℕ} [NeZero N_c] {wab : WilsonPolymerActivityBound N_c}
    (pkg : ShiftedF3MayerCountPackage N_c wab) :
    (countPackage pkg).dim = pkg.dim := rfl

@[simp] theorem ofSubpackages_mayerPackage_countPackage
    {N_c : ℕ} [NeZero N_c] {wab : WilsonPolymerActivityBound N_c}
    (pkg : ShiftedF3MayerCountPackage N_c wab) :
    ofSubpackages (mayerPackage pkg) (countPackage pkg) = pkg := rfl

end ShiftedF3MayerCountPackage

/-- The single-package F3 route yields the Wilson-facing cluster-correlator
bound. -/
theorem clusterCorrelatorBound_of_shiftedF3MayerCountPackage
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : ShiftedF3MayerCountPackage N_c wab) :
    ClusterCorrelatorBound N_c wab.r
      (clusterPrefactorShifted wab.r pkg.C_conn pkg.A₀ pkg.dim) :=
  clusterCorrelatorBound_of_shiftedCountBound_mayerData_ceil
    N_c wab.r wab.hr_pos wab.hr_lt1 pkg.C_conn pkg.A₀ pkg.hC pkg.hA
    pkg.dim pkg.data pkg.h_count

/-- The single-package F3 route yields the older analytic witness bundle. -/
noncomputable def clayWitnessHyp_of_shiftedF3MayerCountPackage
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : ShiftedF3MayerCountPackage N_c wab) :
    ClayWitnessHyp N_c :=
  clayWitnessHyp_of_shiftedCountBound_mayerData_ceil
    N_c wab pkg.C_conn pkg.A₀ pkg.hC pkg.hA pkg.dim pkg.data pkg.h_count

/-- The single-package F3 route yields the authentic mass-gap structure. -/
noncomputable def clayMassGap_of_shiftedF3MayerCountPackage
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : ShiftedF3MayerCountPackage N_c wab) :
    ClayYangMillsMassGap N_c :=
  clayMassGap_of_shiftedCountBound_mayerData_ceil
    N_c wab pkg.C_conn pkg.A₀ pkg.hC pkg.hA pkg.dim pkg.data pkg.h_count

/-- The single-package F3 route yields the connected-correlator-decay hub. -/
noncomputable def clayConnectedCorrDecay_of_shiftedF3MayerCountPackage
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : ShiftedF3MayerCountPackage N_c wab) :
    ClayConnectedCorrDecay N_c :=
  clayConnectedCorrDecay_of_shiftedCountBound_mayerData_ceil
    N_c wab pkg.C_conn pkg.A₀ pkg.hC pkg.hA pkg.dim pkg.data pkg.h_count

/-- The single-package F3 route still projects to the weak theorem endpoint. -/
theorem clay_theorem_of_shiftedF3MayerCountPackage
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : ShiftedF3MayerCountPackage N_c wab) :
    ClayYangMillsTheorem :=
  clay_theorem_of_shiftedCountBound_mayerData_ceil
    N_c wab pkg.C_conn pkg.A₀ pkg.hC pkg.hA pkg.dim pkg.data pkg.h_count

/-- Independently-produced Mayer/activity and count packages yield the
Wilson-facing cluster-correlator bound. -/
theorem clusterCorrelatorBound_of_shiftedF3Subpackages
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : ShiftedF3MayerPackage N_c wab)
    (count : ShiftedF3CountPackage) :
    ClusterCorrelatorBound N_c wab.r
      (clusterPrefactorShifted wab.r count.C_conn mayer.A₀ count.dim) :=
  clusterCorrelatorBound_of_shiftedF3MayerCountPackage N_c wab
    (ShiftedF3MayerCountPackage.ofSubpackages mayer count)

/-- Independently-produced Mayer/activity and count packages yield the older
analytic witness bundle. -/
noncomputable def clayWitnessHyp_of_shiftedF3Subpackages
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : ShiftedF3MayerPackage N_c wab)
    (count : ShiftedF3CountPackage) :
    ClayWitnessHyp N_c :=
  clayWitnessHyp_of_shiftedF3MayerCountPackage N_c wab
    (ShiftedF3MayerCountPackage.ofSubpackages mayer count)

/-- Independently-produced Mayer/activity and count packages yield the authentic
mass-gap structure. -/
noncomputable def clayMassGap_of_shiftedF3Subpackages
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : ShiftedF3MayerPackage N_c wab)
    (count : ShiftedF3CountPackage) :
    ClayYangMillsMassGap N_c :=
  clayMassGap_of_shiftedF3MayerCountPackage N_c wab
    (ShiftedF3MayerCountPackage.ofSubpackages mayer count)

/-- Independently-produced Mayer/activity and count packages yield the
connected-correlator-decay hub. -/
noncomputable def clayConnectedCorrDecay_of_shiftedF3Subpackages
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : ShiftedF3MayerPackage N_c wab)
    (count : ShiftedF3CountPackage) :
    ClayConnectedCorrDecay N_c :=
  clayConnectedCorrDecay_of_shiftedF3MayerCountPackage N_c wab
    (ShiftedF3MayerCountPackage.ofSubpackages mayer count)

/-- Independently-produced Mayer/activity and count packages still project to
the weak theorem endpoint. -/
theorem clay_theorem_of_shiftedF3Subpackages
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : ShiftedF3MayerPackage N_c wab)
    (count : ShiftedF3CountPackage) :
    ClayYangMillsTheorem :=
  clay_theorem_of_shiftedF3MayerCountPackage N_c wab
    (ShiftedF3MayerCountPackage.ofSubpackages mayer count)

/-- The single-package mass-gap endpoint has decay rate `kpParameter wab.r`. -/
theorem clayMassGap_of_shiftedF3MayerCountPackage_mass_eq
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : ShiftedF3MayerCountPackage N_c wab) :
    (clayMassGap_of_shiftedF3MayerCountPackage N_c wab pkg).m =
      kpParameter wab.r := rfl

/-- The single-package mass-gap endpoint has the shifted cluster prefactor. -/
theorem clayMassGap_of_shiftedF3MayerCountPackage_prefactor_eq
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : ShiftedF3MayerCountPackage N_c wab) :
    (clayMassGap_of_shiftedF3MayerCountPackage N_c wab pkg).C =
      clusterPrefactorShifted wab.r pkg.C_conn pkg.A₀ pkg.dim := rfl

/-- The connected-decay endpoint has decay rate `kpParameter wab.r`. -/
theorem clayConnectedCorrDecay_of_shiftedF3MayerCountPackage_mass_eq
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : ShiftedF3MayerCountPackage N_c wab) :
    (clayConnectedCorrDecay_of_shiftedF3MayerCountPackage N_c wab pkg).m =
      kpParameter wab.r := rfl

/-- The connected-decay endpoint has the shifted cluster prefactor. -/
theorem clayConnectedCorrDecay_of_shiftedF3MayerCountPackage_prefactor_eq
    (N_c : ℕ) [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (pkg : ShiftedF3MayerCountPackage N_c wab) :
    (clayConnectedCorrDecay_of_shiftedF3MayerCountPackage N_c wab pkg).C =
      clusterPrefactorShifted wab.r pkg.C_conn pkg.A₀ pkg.dim := rfl

#print axioms clusterCorrelatorBound_of_shiftedF3MayerCountPackage
#print axioms clayWitnessHyp_of_shiftedF3MayerCountPackage
#print axioms clayMassGap_of_shiftedF3MayerCountPackage
#print axioms clayConnectedCorrDecay_of_shiftedF3MayerCountPackage
#print axioms clay_theorem_of_shiftedF3MayerCountPackage
#print axioms clusterCorrelatorBound_of_shiftedF3Subpackages
#print axioms clayWitnessHyp_of_shiftedF3Subpackages
#print axioms clayMassGap_of_shiftedF3Subpackages
#print axioms clayConnectedCorrDecay_of_shiftedF3Subpackages
#print axioms clay_theorem_of_shiftedF3Subpackages
#print axioms shiftedF3MayerPackage_su1_zero
#print axioms ShiftedF3CountPackage.toAt
#print axioms ShiftedF3CountPackage.toAt_C_conn
#print axioms ShiftedF3CountPackage.toAt_dim
#print axioms ShiftedF3CountPackage.toAt_apply
#print axioms ShiftedF3MayerCountPackage.ofSubpackages
#print axioms ShiftedF3MayerCountPackage.mayerPackage
#print axioms ShiftedF3MayerCountPackage.countPackage
#print axioms ShiftedF3MayerCountPackage.ofSubpackages_C_conn
#print axioms ShiftedF3MayerCountPackage.ofSubpackages_A₀
#print axioms ShiftedF3MayerCountPackage.ofSubpackages_dim
#print axioms ShiftedF3MayerCountPackage.ofSubpackages_data
#print axioms ShiftedF3MayerCountPackage.mayerPackage_A₀
#print axioms ShiftedF3MayerCountPackage.mayerPackage_data
#print axioms ShiftedF3MayerCountPackage.countPackage_C_conn
#print axioms ShiftedF3MayerCountPackage.countPackage_dim
#print axioms ShiftedF3MayerCountPackage.ofSubpackages_mayerPackage_countPackage
#print axioms clayMassGap_of_shiftedF3MayerCountPackage_mass_eq
#print axioms clayMassGap_of_shiftedF3MayerCountPackage_prefactor_eq
#print axioms clayConnectedCorrDecay_of_shiftedF3MayerCountPackage_mass_eq
#print axioms clayConnectedCorrDecay_of_shiftedF3MayerCountPackage_prefactor_eq

end YangMills
