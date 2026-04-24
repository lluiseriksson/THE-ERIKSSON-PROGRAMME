/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.ClayCore.MayerExpansion
import YangMills.ClayCore.WilsonClusterProof

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

#print axioms TruncatedActivities.two_point_decay_from_cluster_tsum

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
#print axioms clusterCorrelatorBound_of_truncatedActivities_ceil
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

#print axioms finiteConnectingSum_eq_connectedFiniteSum
#print axioms connectedFiniteSum_eq_cardBucketSum
#print axioms clusterCorrelatorBound_of_connectedFiniteBounds_ceil

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

end YangMills
