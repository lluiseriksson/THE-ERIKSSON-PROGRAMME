# CLUSTER-CORRELATION-PLAN — discharging the IR hypothesis

**Status (2026-06-10):** design document, written at the close of the
session that completed the sharp-KP campaign (`SHARP-KP-PLAN.md` §5h —
volume-uniform convergence of the connected lattice gas, all
oracle-clean).  This plan scopes the next campaign: the
**cluster-correlation chain**, whose endpoint discharges the IR
hypothesis `hIRbound : ∀ d, |covIR d| ≤ C1 · r^d` of
`lattice_mass_gap_of_clustering_uniform` (Paper/ClusteringToGap.lean)
for a concrete lattice correlator.

## 1. What is proved and what is missing

Proved (the engine, all oracle-clean at
`[propext, Classical.choice, Quot.sound]`):

* `kp_pinned_cluster_bound` / `pinned_cluster_summable_sharp`
  (KP/SharpShell.lean): `∑_n pinnedClusterWeight P c n ≤ ‖z(c)‖·e^{a(c)}`
  under the bare `KPCriterion P a`.
* `kp_convergence_sharp` / `kp_norm_clusterSum_le_sharp` (KP/SharpKP.lean).
* `connectedLatticePolymerSystem_kpCriterion_volumeUniform`
  (ConnectedEntropy.lean): the criterion for the connected lattice gas
  with `a(c) = t·|c|`, hypotheses depending only on `d, B, β, t`.
* `connectedLatticeClusterSum_summable_volumeUniform`: the campaign goal.

Missing (this plan): the bridge from `clusterSum`-type objects to
**truncated two-point functions**, and the **distance-decay** of the
connecting part.

## 2. The two halves

### Half A (KP-side, self-contained — do FIRST): size-tail decay

The decay mechanism is purely combinatorial: a cluster whose support
has plaquette-diameter ≥ L has total plaquette count ≥ L/κ(d), so its
weight is exponentially suppressed once activities carry `e^{ε·|·|}`.

**A1 (activity tilting — instantiation, no new KP math).**  For a
polymer system `P` and `ε ≥ 0`, define the tilted system `P_ε` with
`activity_ε(c) := activity(c)·e^{ε·|c|}` (same polymers, same
incompatibility).  Observe:

* `KPCriterion (P_ε) (t·|·|)` follows from the SAME volume-uniform
  entropy proof with `t` replaced by `t + ε` (the per-plaquette
  geometric bound absorbs `e^{(t+ε)|c|}`; the smallness window shifts).
  Formal shape: a new instance of
  `connectedLatticePolymerSystem_kpCriterion_volumeUniform`-style
  reasoning, or better: prove the criterion lemma once with a general
  weight parameter and instantiate twice.
* `pinnedClusterWeight P_ε c n ≥ e^{ε·(n+1)}·pinnedClusterWeight P c n`
  is FALSE as stated (sizes are polymer-counts, the tilt is
  plaquette-counts) — the correct comparison is per-cluster:
  each cluster `X` satisfies
  `∏ ‖z_ε(X_i)‖ = e^{ε·∑|X_i|}·∏ ‖z(X_i)‖ ≥ e^{ε·(total plaquettes)}·∏‖z‖`
  with equality; and `total plaquettes ≥ n + 1` (each polymer nonempty)
  and `total plaquettes ≥ (support diameter)/κ` (connectivity).  Tail
  bounds therefore live at the level of **restricted cluster sums**,
  not the per-size weights.

**A2 (restricted cluster sums + the tail lemma — the new KP brick).**
Define the pinned cluster sum restricted to clusters whose support
meets/leaves a region, or with total plaquette count ≥ L:

    pinnedClusterWeightGE P c L n  :=  same sum, filtered by
      (∑ i, |X i|) ≥ L

Tail lemma (the target of Half A):

    ∑_n pinnedClusterWeightGE P c L n
      ≤ e^{-εL} · ‖z_ε(c)‖ · e^{a_ε(c)}        (A†)

Proof: per cluster, `1 ≤ e^{ε(∑|X_i|) − εL}` on the filtered set;
absorb `e^{ε∑|X_i|}` into the activities (exactly `P_ε`); apply
`kp_pinned_cluster_bound` to `P_ε`.  This is a filter-monotone +
reindexing argument over the proved bound — one brick, no new
combinatorics.  All ingredients exist; the only design point is to
state `pinnedClusterWeightGE` with the filter INSIDE the existing
`pinnedClusterWeight` shape so the comparison is `Finset.sum_le_sum`
on the same index set.

### Half B (L1-side — the genuinely new layer): correlator = connecting clusters

The truncated correlator of two local observables `f, g` supported on
plaquette sets `S_f, S_g`:

    cov(f, g) = ⟨fg⟩ − ⟨f⟩⟨g⟩

For polymer gases with local observables, the standard identity
(Friedli–Velenik §5.7, Ueltschi §4): `log` of the source-deformed
partition function is the cluster sum of the deformed gas, and
`cov(f,g)` is a sum over clusters whose support **connects** `S_f` to
`S_g`.  Every connecting cluster has total plaquette count
`≥ dist(S_f, S_g)/κ(d)` — feed (A†).

Formal route, in dependency order:

* **B1 (deformed gas):** source-deformed activities
  `z_s(c) := z(c)·(1 + s·δ[c touches S])` or the two-parameter version;
  the existing `PolymerExpansion`/`PolymerFactorization` layer already
  proves `Z = polymer partition function` — verify the deformation
  stays inside `connectedLatticePolymerSystem`'s shape (it rescales
  plaquette weights, so it should be the SAME construction at a
  modified `pe`; check `pe`-genericity of the factorization).
* **B2 (derivative identity at finite truncation):** `∂_s∂_u log Z(s,u)`
  at `s=u=0` = sum over clusters touching both supports.  AVOID real
  derivatives: state the identity at the level of **formal differences**
  (the coefficient extraction is finite-dimensional polynomial algebra
  in finite volume) or work with explicit two-cluster expansions.
  DESIGN DECISION DEFERRED: pick between (i) polynomial-coefficient
  formalization, (ii) the Duhamel/two-system trick
  (cov = Z-weighted difference of two gases), (iii) direct
  combinatorial covariance expansion.  Each is multi-session; (iii)
  has the most precedent in the repo (everything is finite sums).
* **B3 (geometry):** connecting clusters are large:
  `IsCluster + touches S_f + touches S_g → ∑|X_i| ≥ dist/κ` — uses the
  walk/connectivity machinery of ConnectedEntropy.lean
  (`exists_covering_lazyWalk`, crossing lemmas).  Class B, bounded.
* **B4 (endpoint):** `|cov(f,g)| ≤ C·e^{-m·dist}` with `C, m` from
  `d, B, β, t` only; instantiate `hIRbound` of
  `lattice_mass_gap_of_clustering_uniform`.

## 2b. Half A status — CLOSED at the abstract level (2026-06-10, same
session as the plan; `KP/ClusterTail.lean`, commit `112c2d2`)

`PolymerSystem.tilt` (ursell invariant — literally `rfl`),
`tilt_norm_activity`, `pinnedClusterWeightGE` (+ nonneg),
`pinnedClusterWeightGE_le_tilt`, and **`kp_pinned_cluster_tail_bound`**
(A†) are all proved and oracle-clean.

**Half A is now FULLY closed including the lattice level**
(commit `aaa6804`):
`connectedLatticePolymerSystem_tilt_kpCriterion_volumeUniform`
(ConnectedEntropy.lean — the criterion proof body replicated with
`x := (e^{|β|B}−1)·e^{t+ε}` and the tilted `hterm`; the tilt and the
weight combine into one exponential so only the smallness window
shifts) and **`connectedLattice_pinned_tail_volumeUniform`** — the
exponential size-tail `e^{-εL}` for the connected lattice gas with all
constants depending only on `d, B, β, t, ε`.  Next: Half B
(B3 geometry, then the B2 design decision).

Parser note for the next session: long `∑ X ∈ (… : …).filter (…)`
terms as `calc` HEADS need continuation lines indented deeper than the
`∑` token, or the application after `.filter` fails to parse
("unexpected '('; expected ','").  Tactic-form (`refine le_trans …`)
avoids the issue entirely — prefer it for these shapes.

## 2c. B2 design DECISION (2026-06-10, same session): route through
B0 — the Mayer–Ursell inversion

**Finding (audited):** `Ξ = exp(clusterSum)` (E3) is OPEN in the repo —
`Expansion.lean` has only the empty-system base case
(`expansion_identity_isEmpty`) and the first-order check
(`clusterSum_first_order`); `partition_singlePolymer_eq_exp` covers one
polymer.  EVERY covariance route consumes this identity.  So Half B
reorders: **B0 first**, then B1/B3/B4 with the covariance realized as a
log-difference of partition functions (= difference of cluster sums
= connecting-cluster sums, fed to the tail bound).

**B0 (the fundamental theorem of cluster expansion, finite systems):**

* **B0a — the combinatorial heart (the partition identity):** for every
  tuple `X : Fin n → P.Polymer`,

      ∑_{π : Finpartition (univ : Finset (Fin n))}
          ∏_{B ∈ π.parts} ursell(X ∘ orderEmb_B)
        = if (∀ i ≠ j, ¬ P.incomp (X i) (X j)) then 1 else 0

  Proof shape: the RHS is `∑_{E ⊆ edges(G_X)} (−1)^{|E|}` by
  `Finset.sum_powerset_neg_one_pow_card` (EXISTS —
  `Mathlib/Data/Nat/Choose/Sum.lean:218`) + the edgeFinset-emptiness
  characterization; group `E` by the **component partition** of the
  spanning subgraph `(Fin n, E)` (reachability classes — the `reachSet`
  machinery of `UrsellRecurrence.lean` is the precedent); the fiber over
  `π` is the product over blocks of connected edge-sets, i.e.
  `∏_B ursell` after relabeling each block by `Finset.orderIsoOfFin`
  (transport precedented by `markedEmb`/`subtree_prod_transport` in
  SharpShell).  `Fintype (Finpartition s)` EXISTS.
* **B0b — the analytic resummation:** `exp(K) = ∑_k K^k/k!`; Cauchy-
  multiply truncated cluster sums; regroup k-tuples-of-clusters into the
  concatenated tuple with the multinomial as an EQUALITY (the O5b/per_k
  machinery shape: piFinset boxes + factorial bookkeeping); apply B0a
  per concatenated tuple; recognize `partition P univ`
  (`∑_{S admissible} ∏ z` — note `Admissible` is about Finsets, the
  tuple-side carries `n!/multiplicities` symmetry factors; multiplicity
  ≥ 2 dies by hard-core `incomp_self` through B0a's indicator).
  Absolute convergence everywhere from `kp_convergence_sharp` (PROVED).

Budgets: B0a 4–7 cycles; B0b 6–12 cycles (the hardest analysis left on
this chain).  Both volume-free, abstract-KP level.

## 3. Order of work and budgets

1. A2 tail lemma (with A1 tilting as its engine): 2–3 cycles.
   **DONE except the lattice criterion instantiation (above).**
2. B3 geometry: 1–2 cycles.
3. B1 deformation audit: 1 cycle (reading + small lemmas).
4. B2: the hard half; design session first (pick (i)/(ii)/(iii)),
   then likely 5–10 cycles.
5. B4 composition: 1 cycle.

## 4. Honesty invariant

All of this is M3 lattice-side (the IR input of the conditional
mass-gap theorem).  The UV hypothesis (§6.3 of the paper) is separate
content, not yet in the repo.  None of this reduces M4/M5/Clay
(continuum limit, OS reconstruction, continuum gap — open
mathematics).  Distance to Clay: **~0% (<0.1%)** — keep it written
everywhere.
