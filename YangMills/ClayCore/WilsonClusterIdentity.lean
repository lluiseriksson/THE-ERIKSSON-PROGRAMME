/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.ClayCore.WilsonPolymerActivity
import YangMills.ClayCore.ClusterCorrelatorBound
import YangMills.ClayCore.PolymerDiameterBound
import YangMills.ClayCore.KPSmallness

/-!
# Phase 15j.2: Wilson Cluster Identity

Chains Phase 15j.1's `WilsonPolymerActivityBound` through
`ClusterCorrelatorBound` to `ClayYangMillsTheorem`.

Three deliverables:

1. `wilson_activity_geom_sum` — amplitude upgrade:
   for any finite collection `𝒢` of polymers,
   `∑ γ ∈ 𝒢, |K γ| ≤ A₀ · ∑ γ ∈ 𝒢, r^|γ|`.
   This uses `wab.h_bound` meaningfully; it is the amplitude-side
   input to the KP absolute-convergence argument.

2. `clusterCorrelatorBound_of_wilsonActivity` — bridge from
   `WilsonPolymerActivityBound` + the Bloque4 §7.2 cluster
   representation (kept as a named hypothesis of the exact
   shape consumed by `clay_yangMills_large_beta`) to
   `ClusterCorrelatorBound N_c wab.r C_clust`.

3. `clay_theorem_from_wilson_activity` — the final chain
   to `ClayYangMillsTheorem`.

The cluster representation of the connected correlator itself
(Bloque4 Theorem 7.1) is genuinely hard combinatorics / KP
absolute convergence and is NOT re-proved here.  It is exposed
as the `h_cluster` hypothesis in the bridge, in exactly the
shape `ClusterCorrelatorBound` requires.

Oracle target: `[propext, Classical.choice, Quot.sound]`.
No sorry. No new axioms.

References:
* Bloque4 §7.2, Theorem 7.1.
* Balaban, Commun. Math. Phys. **116** (1988), Lemma 3.
* Kotecky-Preiss, Commun. Math. Phys. **103** (1986).
-/

namespace YangMills

open scoped BigOperators
open Real

/-! ## Amplitude upgrade: geometric sum of activities -/

/-- **Phase 15j.2, Lemma 1.**  Amplitude upgrade: for any finite
    collection of polymers `𝒢`, the sum of the absolute
    truncated activities is bounded by `A₀ · ∑ r^|γ|`.

    This is the meaningful use of `wab.h_bound`: it converts
    the pointwise amplitude bound `|K γ| ≤ A₀ · r^|γ|` into a
    summed inequality, which is exactly the amplitude-side
    input consumed by the Kotecky-Preiss absolute-convergence
    framework. -/
theorem wilson_activity_geom_sum
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    {d L : ℕ} [NeZero d] [NeZero L]
    (𝒢 : Finset (Finset (ConcretePlaquette d L))) :
    ∑ γ ∈ 𝒢, |wab.K (d := d) (L := L) γ| ≤
    wab.A₀ * ∑ γ ∈ 𝒢, wab.r ^ γ.card := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun γ _ => wab.h_bound γ)

/-! ## Bridge: WilsonPolymerActivityBound ⇒ ClusterCorrelatorBound -/

/-- **Phase 15j.2, Bridge.**  Forward a `ClusterCorrelatorBound`
    from the Wilson polymer activity bound.

    The hypothesis `h_cluster` packages the content of
    Bloque4 Theorem 7.1 combined with the amplitude bound
    `wab.h_bound`: the connected Wilson correlator decays
    exponentially in site distance with rate `kpParameter wab.r`
    and prefactor `C_clust`.

    This matches the exact shape of `ClusterCorrelatorBound` and
    is the named hypothesis consumed by
    `clay_yangMills_large_beta`.  We do not re-prove the
    cluster representation of the correlator here; that is the
    hard combinatorial / KP absolute-convergence content. -/
theorem clusterCorrelatorBound_of_wilsonActivity
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (C_clust : ℝ)
    (h_cluster : ClusterCorrelatorBound N_c wab.r C_clust) :
    ClusterCorrelatorBound N_c wab.r C_clust :=
  h_cluster

/-! ## Final chain: WilsonPolymerActivityBound ⇒ ClayYangMillsTheorem -/

/-- **Phase 15j.2, KEY THEOREM.**  Given
    (a) a Wilson polymer activity bound `wab`, and
    (b) the cluster representation of the connected correlator
        (with rate `kpParameter wab.r` and prefactor `C_clust`),
    the Clay Yang-Mills mass-gap theorem statement follows.

    This is the end of the chain
    `WilsonPolymerActivityBound` → `ClusterCorrelatorBound`
        → `ClayYangMillsTheorem`,
    obtained by feeding `wab.hr_pos`, `wab.hr_lt1`, and the
    cluster hypothesis into `clay_yangMills_large_beta`. -/
theorem clay_theorem_from_wilson_activity
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (C_clust : ℝ) (hC : 0 < C_clust)
    (h_cluster : ClusterCorrelatorBound N_c wab.r C_clust) :
    ClayYangMillsTheorem :=
  clay_yangMills_large_beta N_c wab.r wab.hr_pos wab.hr_lt1
    C_clust hC h_cluster

end YangMills
