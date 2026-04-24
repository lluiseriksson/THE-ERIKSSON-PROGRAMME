/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.ClayCore.MayerExpansion

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

end YangMills
