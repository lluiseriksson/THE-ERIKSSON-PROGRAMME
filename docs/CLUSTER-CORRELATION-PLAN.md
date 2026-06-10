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

**B0a progress (2026-06-10, same session; `KP/MayerInversion.lean`,
commits `6074b9c..4253225`, all oracle-clean):**

* Step 0: `PairwiseCompatible`, `edgeFinset_eq_empty_iff`,
  `sum_neg_one_pow_eq_indicator` (the ungrouped side).
* Step 1: `ursell_comp_equiv` — relabeling invariance via
  `Finset.sum_nbij'` with `Sym2.map`-image bijections,
  `Iso.connected_iff`, `fromEdgeSet_adj` transport.
* Step 2: `reachable_of_walk_image` (walk pullback along an embedding —
  image edge sets never leave the range; walk-induction with
  `Sym2.eq_iff` case split) and `reachable_image_iff` (both
  directions; pushforward via `Reachable.map` with an INLINE hom
  literal `⟨⇑f, hmaprel⟩` — a `have`-bound hom is opaque and its
  coercion will NOT reduce, a hard-won idiom).

**B0a progress, continued (same session, commits `043896a..f30641e`):**

* Step 3 CLOSED: **`sum_blockConnected_eq_ursell`** — the per-block
  identification (image/preimage-filter bijection with the retraction
  lemma `hretract`; `reachable_image_iff`; `connected_iff` +
  `card_pos`).  Hard-won: filter binders over edge-set Finsets MUST be
  type-annotated `(fun E : Finset (Sym2 (Fin n)) => …)` or the
  elaborator drifts to `Set`-typed binders and inserts powerset
  coercion images.  Statement needs `hB : B.Nonempty` (for `B = ∅` the
  LHS is 1 but `ursell` on `Fin 0` is 0).
* Step 4a CLOSED: `reachable_filter_of_closed` (walks never leave
  adjacency-closed sets — `[propext, Quot.sound]`-pure),
  `componentPartition` (`Finpartition.ofSetoid` on
  `reachableSetoid`), `mem_componentPartition_part_iff`,
  `componentPartition_part_closed`, `componentPartition_edge_same_part`.

**B0a — COMPLETE (2026-06-10, same session; commits up to `1999108`,
all oracle-clean).**  The fibration core landed in four committed
sub-bricks: A1 `filter_within_mem_of_cp_eq`, A2
`biUnion_filter_within_parts` + `filter_within_disjoint`, A3
`componentPartition_biUnion_eq` (+ `mem_of_reachable_closed`;
partition equality via pointwise part equality →
`nonempty_of_mem_parts`/`part_eq_of_mem` double inclusion →
`Finpartition.ext`; Finpartition lemmas need DOT-NOTATION — the bare
names mis-slot), A4 **`fiber_cp_factorization`** ((★); `Finset.prod_sum`
to the `parts.pi`-side, `sum_nbij'` with within-part filters vs
`dif`-totalized `biUnion`s, card additivity by `card_biUnion`,
`prod_pow_eq_pow_sum`, `prod_attach`), and the endpoint
**`ursell_partition_identity`**:

    ∑_{π : Finpartition univ} ∏_{B ∈ π.parts} ursell(X∘orderIsoOfFin B)
      = 𝟙[X pairwise compatible]

**NEXT: B0b** (the analytic resummation to `Ξ = exp(clusterSum)`) —
see §2c.  All combinatorial inputs are now on the shelf.

## 2d. B0b — the full design (2026-06-10, written after B0a closed)

**The chain** (every infinite rearrangement justified by absolute
convergence from `kp_convergence_sharp` + norm bounds):

1. **exp expansion:** `Complex.exp K = ∑'_k K^k/k!`
   (`NormedSpace.exp`/`Complex.exp_eq_tsum`-form; verify exact name).
2. **Power Fubini (B0b-1):** `K^k = ∑'_{f : Fin k → ℕ} ∏_i a_{f i}`
   where `a_n := ((n+1)!)⁻¹·∑_{X : Fin (n+1) → P} φ(X)·∏z`.
   By induction on `k`: `Summable.tsum_mul_tsum_of_summable_norm`
   (ℂ, absolute convergence) + reindex `ℕ × (Fin k → ℕ) ≃ (Fin (k+1) → ℕ)`
   (`Fin.consEquiv`-style).
3. **Inner expansion:** each `∏_i a_{f i}` is `(∏(f i + 1)!)⁻¹` times a
   finite product of finite sums = sum over tuples-of-tuples
   (`Finset.prod_univ_sum`).
4. **Multinomial regrouping (B0b-2, finite combinatorics):** for sizes
   `m : Fin k → ℕ` (`m i ≥ 1`), `N := ∑ m i`:

       ∑_{(X,(B_i))} ∏_i F_i(X ∘ emb_{B_i}) = M(m) · ∑_{(X_i)} ∏_i F_i(X_i)

   where the left sum is over `X : Fin N → Polymer` times ORDERED
   set-partitions `(B_i)` of `Fin N` with `|B_i| = m i`, `emb_B` is
   `orderIsoOfFin`, and `M(m)·∏(m i)! = N!` (exact multinomial count —
   prove multiplicatively, no division; the `card_blockData_mul_le`
   pattern but as an equality: ordered partitions × per-block
   enumerations ≃ bijections `Fin N ≃ Fin N`).
   Per (X,(B_i)) the assembled X is determined by the subtuples and the
   partition — the fiber over `(X_i)` is exactly the partitions.
5. **Ordered → unordered (B0b-3):** per fixed `X : Fin N → Polymer`,
   `∑_k (1/k!)·∑_{ordered k-block partitions} ∏φ-blocks
     = ∑_{π : Finpartition univ} ∏_{B ∈ π.parts} φ(X|_B)`
   (each unordered π with `k` parts has exactly `k!` orderings —
   `card_enumerations`-style; sizes vary per block, no per-`m` claim —
   the §5c-correction lesson applies here too).
6. **The partition identity (PROVED):** the π-sum is
   `𝟙[PairwiseCompatible X]`.
7. **Injective collapse (B0b-4):** pairwise-compatible tuples are
   INJECTIVE (hard core: a repeat would be self-incompatible), so
   `(1/N!)·∑_{X compatible} ∏z = ∑_{S admissible, |S|=N} ∏z`
   (each admissible `N`-set has exactly `N!` enumerations —
   `card_enumerations` again); summing over `N` gives
   `partition P univ` (the `N = 0` term ↔ the `k = 0` exp term ↔ the
   empty admissible set).
8. **Assembly (B0b-5):** the (k, sizes, tuples) triple tsum rearranges
   to the N-graded sum — `tsum` over a sigma/equiv with absolute
   convergence; the infinite non-compatible tail vanishes TERMWISE
   after step 6 (only finitely many `N ≤ #Polymer` survive).

Order of work: B0b-2 and B0b-3 first (finite combinatorics, fully in
the house style); then B0b-4 (small); then the analytic shell
B0b-1/B0b-5 around them; step 1 last (glue).  Budgets: 2–3 cycles for
each of B0b-2/3/4; 4–8 for the analytic shell.

**(historical) Remaining-work list before the above was closed:**

1. (★) per-π fiber factorization:
   `∑_{E ⊆ edgeFinset(G_X) : componentPartition E = π} (−1)^{|E|}
     = ∏_{B ∈ π.parts} (blockConn-sum B)`.
   Bijection: `E ↦ (fun B _ => E.filter (fun e => ∀ u ∈ e, u ∈ B))`
   into `π.parts.pi (blockConn-sets)`, with `Finset.prod_sum` for the
   product-of-sums ↔ choice-function side.  Ingredients all proved:
   within-part edges (`componentPartition_edge_same_part` + part
   disjointness), per-part connecting (`reachable_filter_of_closed`
   with part-closure), union reconstruction (`Finset.biUnion` over
   `parts.attach`), cardinality additivity (`Finset.card_biUnion` on
   disjoint within-part sets), `(−1)^{∑} = ∏(−1)^{·}`.
   The delicate spot: `componentPartition U = π` for the reconstructed
   union `U`.  **API verified present** (Finpartition.lean): `@[ext]`
   on the structure (parts-equality suffices, proofs irrelevant),
   `part_mem` (`P.part a ∈ P.parts ↔ a ∈ s`), `part_eq_iff_mem`,
   `part_eq_of_mem`, `part_surjOn` (every part is some `P.part a`),
   `Finpartition.disjoint` (parts pairwise disjoint), `mem_part`.
   Route: prove the POINTWISE class equality
   `(componentPartition U).part a = π.part a` (reachability-in-`U` ↔
   same-`π`-part, via `reachable_filter_of_closed` and the per-part
   `g B`-connectivity), then parts-sets equal by double inclusion
   through `part_surjOn` + `part_eq_of_mem`, then `Finpartition.ext`.
2. Fibration of the powerset sum over `π` (ite-collapse idiom — sum
   over `Finpartition univ`, a Fintype) + compose with
   `sum_neg_one_pow_eq_indicator` and step 3 → the partition identity.
3. Then B0b (the analytic resummation).

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
