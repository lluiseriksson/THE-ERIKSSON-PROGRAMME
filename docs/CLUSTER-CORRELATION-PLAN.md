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

**B0b progress (2026-06-10, same session; commits `3c48c95`,
`cddfc09`, oracle-clean):**

* B0b-4 CLOSED: `PairwiseCompatible.injective` +
  `sum_pairwiseCompatible_eq` (compatible-tuple activity sums = `N!`
  times admissible-set sums at cardinality `N`; image-fibration via
  the ite-collapse + `card_enumerations`; the lemma needs
  `[Fintype P.Polymer]`).
* B0b-3 engine CLOSED: `sum_symmetrize_gen` — the SharpShell
  symmetrization at arbitrary finite codomain and `ℂ`-values
  (verbatim adaptation; `card_enumerations(_ne)` were already generic).
  Its application to partitions: `α := Finpartition univ`,
  `β := Finset (Fin N)`, `S := Finpartition.parts`,
  `nmax := N` — needs `π.parts.card ≤ N` (check
  `Finpartition.card_parts_le_card` or derive from
  `∑_{B ∈ parts} 1 ≤ ∑ |B| = N`); enumerations of `π.parts` ARE the
  ordered partitions with part-set `π.parts`.
* NEXT: **B0b-2** (the multinomial regrouping — the remaining big
  finite brick), in the REFINED formulation below, then the analytic
  shell B0b-1/B0b-5.

**B0b-2/5 REFINED DESIGN (2026-06-10, supersedes §2d step 4's
`(X,(B_i))`-formulation; derived by walking the assembly backwards):**

Define `IsOrdPartition (σ : Fin k → Finset (Fin N)) :=
(∀ i, (σ i).Nonempty) ∧ (∀ i j, i ≠ j → Disjoint (σ i) (σ j)) ∧
univ.biUnion σ = univ`.  The per-`N` chain after the partition
identity is:

  (i)   `∑_π ∏_{B∈π.parts} φ(X|_B)` → `sum_symmetrize_gen` (PROVED)
        with `S := Finpartition.parts`, `nmax := N` (need
        `π.parts.card ≤ N` — from `∑_{B∈parts} 1 ≤ ∑ |B| = N`).
  (ii)  Per (π, enumeration σ of π.parts): `∏_{B∈parts} = ∏_i (X|σᵢ)`
        (`Finset.prod_image`-transport along injective σ), then
        collapse the π-sum: enumerations of partitions' parts =
        `IsOrdPartition` tuples (build the `Finpartition` FROM σ:
        parts := image σ; `supIndep_iff_pairwiseDisjoint`,
        `sup_eq_biUnion`, nonempty ⇒ `∅ ∉`; the ite-collapse idiom,
        σ determines its π).
  (iii) **The X-split (exact, bijective):** for σ with
        `IsOrdPartition`, `m i := (σ i).card`:
        `∑_{X : Fin N → P} ∏_i G_i(X ∘ emb_{σ i}) · (weights split)
          = ∏_i ∑_{X_i : Fin (m i) → P} G_i(X_i)`
        via `sum_nbij'` with restriction/assembly maps
        (`Finset.prod_biUnion` splits `∏_j z(X j)` over the disjoint
        cover).  After this the σ-dependence is SIZES ONLY.
  (iv)  **The multinomial count (the genuine new content):**
        `#{σ // IsOrdPartition σ ∧ ∀ i, |σ i| = m i} · ∏ (m i)! = N!`
        — EQUALITY, via the explicit equivalence
        `(Σ σ ∈ ordp(m), Π i, enumerations(σ i)) ≃ ((Σ i, Fin (m i)) ≃ Fin N)`:
        forward = concatenation along `finSigmaFinEquiv`-offsets,
        backward = per-interval images/restrictions; then
        `Fintype.card_sigma` + `Fintype.card_piFinset` +
        `card_enumerations` (= ∏ mᵢ!) on the left and
        `Fintype.card_equiv` (= N!) on the right.  MINE
        `card_blockData_mul_le`'s proof (SharpShell ~line 869) for the
        placement-map machinery — it built the INJECTION half of this
        equivalence already; the surjectivity half is new.
  (v)   Fiber the σ-sum by the size vector (ite-collapse), apply (iv),
        cancel `(1/N!)·N!/∏ mᵢ!` against the exp-side
        `∏ 1/(f i + 1)!` at `m i = f i + 1` (blocks nonempty ⇒ sizes
        ≥ 1 ⇔ the `n+1`-indexing of `clusterSum`'s tuples).
  (vi)  Analytic shell (B0b-1/B0b-5): exp series + k-fold tsum Fubini
        + the (k, m)-to-N regrouping of the double tsum; all
        rearrangements by absolute convergence (`kp_convergence_sharp`
        + termwise norm bounds).

Budgets: (i)-(ii) 1–2 cycles; (iii) 1–2; (iv) 3–5 (the big one);
(v) 1–2; (vi) 4–8.

**Progress (same session, commits `cd43ae6`, `dcfdbd1`, `b039e99`,
oracle-clean):** (i)–(iii) CLOSED — `IsOrdPartition` (+ `.injective`,
`.toBlockData`), `parts_card_le`, `finpartitionOfOrd` (+ parts simp),
**`sum_finpartition_eq_ordPartitions`** (the π-collapse; note
`disjoint_self` is the ORDER-level name, and the biUnion/image bridge
is `Finset.image_biUnion`), `sum_coverSplit_complex`, and
**`sum_split_ordPartition`** (the X-split).  X-split idiom worth
keeping: build ONE composite equiv
(`arrowCongr subtypeUnivEquiv` → `coverSplitEquiv` → `piCongrRight
arrowCongr orderIsoOfFin.symm`) so every SUM in the statement lives on
Fin-function spaces — separately-stated subtype-function sums hit
Classical-vs-derived instance seams that `sum_congr rfl` cannot cross;
with calc-spelled sides the value tracking is fully definitional
(per-point `rfl`).

**(iv) CLOSED (commit `0aea842`, oracle-clean):**
`enumTuplesEquivSigma` — FLATTEN the data: tuples of per-block
injections with pairwise-disjoint ranges ≃ bijections
`(Σ i, Fin (m i)) ≃ Fin N` directly (the image-partitions are
determined by the tuples, so NO sigma-of-subtypes and no HEq anywhere;
`left_inv`/`right_inv` are `rfl`-level).  Then
**`card_ordPartition_mul`** (`#ordp(m)·∏ mᵢ! = N!`, an equality) by
counting the tuple filter two ways: `Fintype.card_equiv` +
`equivOfCardEq` on the bijection side;
`Finset.card_eq_sum_card_fiberwise` over image partitions with
`piFinset`-fibers and `card_enumerations` on the other.

Remaining: (v) cancellation, (vi) the analytic shell — bookkeeping and
standard tsum work; ALL hard combinatorics of `Ξ = exp(clusterSum)` is
now machine-checked.

**(v-a)+(v-b) CLOSED (commit `66c7555`, oracle-clean):**
`prod_split_ordPartition` (the z-product cover split) and
`sum_ordp_fiber_sizes` (the size fibration with class-count
coefficients).  **What remains of (v): the per-`N` master calc**
gluing the proved bricks in order — per `X`: `ursell_partition_identity`
→ `sum_finpartition_eq_ordPartitions` (h := fun B => φ(X|_B)) → swap →
per-(k,σ): `prod_split_ordPartition` on the z-product, then
`sum_split_ordPartition` with `G m Y := (ursell P Y : ℂ)·∏ z(Y l)` →
`sum_ordp_fiber_sizes` with `W m := ∑_Y G m Y` → `card_ordPartition_mul`
(divide through: `(count : ℂ) = N!/∏ mᵢ!`, casts via
`Nat.cast_mul`/`field_simp`) → endpoint shape:

    (1/N!)·A_N = ∑_{k ≤ N} (1/k!) ∑_{m-filter} ∏ᵢ (W(mᵢ)/mᵢ!)

with `A_N = ∑_X 𝟙[compat]·∏z = N!·(admissible-set sum)` (B0b-4).
Then (vi): the tsum shell (exp series + k-fold Fubini + (k,m)→N
regrouping; absolute convergence from `kp_convergence_sharp`).

**M-a CLOSED (commit `9f85611`, oracle-clean):** `indicator_eq_ordp`
(externalize per-point instance-heavy lemma applications as STANDALONE
lemmas — the per_k lesson recurred: a `.trans` against the
`Finpartition`-instanced sum inside the big theorem melts isDefEq;
also: `simp only [] at hii` to beta the instantiated lemma, and pin
implicit `(N := N)` BEFORE the `↥B → Fin N` coercion fires or it
sticks on metavariables) and **`sum_compat_eq_ordp`** — the finite
heart: `∑_{X compat} ∏z = ∑_k (1/k!) ∑_{σ ordp} ∏ᵢ W((σ i).card)`
with `W m = ∑_{Y : Fin m → P} φ(Y)·∏z(Y)`.

**M-b CLOSED (commit `75f0597`, green on FIRST build, oracle-clean):**
**`admissible_card_sum_eq`** — the per-`N` endpoint:

    ∑_{S admissible, |S| = N} ∏z
      = ∑_{k ≤ N} (1/k!) ∑_{m : sizes, ∑mᵢ = N} ∏ᵢ (W(mᵢ)/mᵢ!)

— the `N`-th coefficient identity of `Ξ = exp(clusterSum)`.  **THE
ENTIRE FINITE HALF OF THE MAYER–URSELL INVERSION IS MACHINE-CHECKED.**

**Remaining: (vi) only** — the tsum shell:
1. DONE (commit `f59918f`): `partition_univ_eq_sum_card` +
   **`partition_univ_eq_cluster_layers`** — `Ξ` in the fully finite
   `N`-graded cluster-layer form.
2. `exp (clusterSum P) = ∑'_k (1/k!) K^k`, `K^k` by induction with
   `Summable.tsum_mul_tsum_of_summable_norm` + `Fin.cons`-reindexing,
   inner finite products expanded; regroup the (k, f)-tsum by
   `N := ∑ (f i + 1)` and match `admissible_card_sum_eq` termwise
   (note `W(m)/m! = a_{m-1}`, the `clusterSum`-term, and the
   `m-filter` with `mᵢ ≥ 1` bijects with `f : Fin k → ℕ` via
   `mᵢ = f i + 1`); the `N > #Polymer` tail vanishes since admissible
   sets are subsets of the polymer type.  Absolute convergence
   everywhere from `kp_convergence_sharp`'s summability.

   **E1 CLOSED (commit `d83a3f7`):** `consE`,
   `summable_norm_prod_pow`, `tsum_pow_eq_tsum_pi`.  Analysis-layer
   pathologies paid for: `Fin.consEquiv` whnf-grinds — hand-roll a
   non-dependent equiv; `Finite (Fin 0 → ℕ)` instance search melts —
   use `hasSum_single`/`tsum_eq_single` at the unique point;
   `Summable.mul_norm` is an HOU sink — pin `(f := ..) (g := ..)`.
   **Remaining for the theorem:** the Ω-architecture —
   `Ω := Σ k, (Fin k → ℕ)`, `H ⟨k,f⟩ := (k!)⁻¹·∏ a (f i)`.
   **E2 CLOSED** (`1f8b9f4`): E1 genericized to `NormedCommRing` +
   `summable_H` (`summable_sigma_of_nonneg` + comparison with
   `Real.summable_pow_div_factorial` via the ℝ-power-Fubini at norms).
   **E3 CLOSED** (`cb497d3`): `exp_tsum_eq_tsum_H` —
   `exp(∑'a) = ∑'_Ω H` (`Complex.exp_eq_exp_ℂ` +
   `NormedSpace.exp_eq_tsum_div` + E1b + `Summable.tsum_sigma`).
   **B0 IS COMPLETE (commit `e879b6b`, all oracle-clean).**
   E4a (`e4c1dd5`): `tsum_H_eq_tsum_layers` (the size regrouping;
   Ω-fibers via `Fintype.subtype` of filtered sigma-candidates).
   E4b (`e879b6b`): `layer_shift` (the `f ↔ m` reindex) and
   **`partition_eq_exp_clusterSum`** — `Ξ = exp(clusterSum)` for any
   finite polymer system with absolutely convergent cluster series.
   **THE FUNDAMENTAL THEOREM OF CLUSTER EXPANSIONS — the months-long
   crux flagged in `Expansion.lean` — IS MACHINE-CHECKED.**
   The KP-instantiated capstone is ALSO CLOSED (`b8dd5ee`):
   `partition_eq_exp_clusterSum_of_kp`.

   **B3 opened (commit `2f93e0b`, oracle-clean):**
   `L1_GibbsMeasure/ClusterGeometry.lean` — `touchGraph`,
   `touchGraph_dist_lt_card_of_connected` (B3a; subtype-walk
   pushforward needs a `show`-unfold of `touchGraph` before
   `fromRel_adj`), `exists_touching_of_not_disjoint` (B3b).
   **B3 COMPLETE (commit `74cac7e`, oracle-clean):**
   `exists_touchWalk_of_connected` (B3a walk form),
   `exists_walk_through_cluster` (the threading — WALK-based, not
   dist-triangle-based: `SimpleGraph.dist` is junk-valued on
   unreachable pairs so the triangle inequality is a trap; `IsPath`
   via `Walk.bypass` keeps the size accounting linear), and
   **`cluster_dist_le`**:
   `(touchGraph d N).dist p q ≤ 2·∑ᵢ (X i).1.card` for any cluster of
   the connected gas touching both plaquettes.  Contrapositive feeds
   Half A: clusters touching p and q have total size
   `≥ dist(p,q)/2`, so the `pinnedClusterWeightGE`-tail at
   `sz c := c.1.card`, `L := dist/2` bounds the connecting-cluster
   sums by `e^{-ε·dist/2}` — volume-uniformly.
   **THE BRIDGE is also closed (commit `c707e06`):**
   `connecting_pinned_le_GE` — pinned cluster sums restricted to
   clusters touching a distant plaquette ≤ `pinnedClusterWeightGE` at
   `L = dist(p,q)/2` (non-clusters vanish termwise, the cluster filter
   lands in the GE filter via `cluster_dist_le`; beware the
   beta-atom/omega mismatch — bridge `∑ (fun c' => …) (X i)` to the
   reduced form with an `rfl`-have).  Composing with
   `pinned_cluster_tail_summable` (Half A) gives per-`c`
   connecting-sum decay `e^{-ε·dist/2}` immediately.

   **THE SUMMED FORM IS CLOSED (commit `0afa558`):**
   **`connecting_cluster_decay`** — the total pinned cluster sum
   through `p`, restricted to clusters touching `q`, decays as
   `e^{-ε·dist(p,q)/2} · x/(1−(16d+1)²x)` at
   `x = (e^{|β|B}−1)e^{t+ε}` — every constant depending only on
   `d, B, β, t, ε`.  **THE IR DECAY MECHANISM IS FULLY
   MACHINE-CHECKED AT THE CLUSTER LEVEL.**

   **Remaining: B1/B2/B4 only** — the measure-side identification.

## 2e. The measure-side campaign — design (2026-06-10, audited)

**Audit finding:** before any covariance identification, the polymer
representation's STEP 2 must be closed:
`partitionFunction = partition P univ` (the lattice `Z` equals the
abstract polymer `Ξ` of the connected gas).  What exists:
`partitionFunction_eq_sum_plaquetteSets'`
(`Z = ∑_{S ⊆ plaquettes} ∫ ∏_{p∈S} f_p`) and — READY IN EXACTLY THE
NEEDED FORM — `integral_prod_prod_plaquetteWeight_of_pairwiseDisjoint`
(`∫∏_C∏ f = ∏_C ∫∏ f` over support-disjoint families).  The NEW work
is the **component bijection**: plaquette sets `S` ↔ admissible
families `A` of connected polymers, via
`S ↦ (touching-components of S)` and `A ↦ ⋃ A` — a BIJECTION (each
`S` decomposes uniquely; every admissible family unions back), so a
single `sum_nbij'`, with values matched by the integral
factorization.  The component machinery mirrors B0a's
(`Finpartition.ofSetoid` on the reachability setoid of the touching
graph restricted to `↥S`; the parts, coerced back to
`Finset (ConcretePlaquette d N)`, are the components — nonempty ✓
connected ✓ pairwise non-touching ✓ admissible ✓).  Budget: 4–8
cycles (the component API is the bulk).

**Step 2 OPENED (commit `2ccc561`, five lemmas green on FIRST
build):** `plaqComponents` + `_nonempty`/`_subset`/`_biUnion`(cover)/
`_not_touching`/`_support_disjoint` in
`L1_GibbsMeasure/ClusterGeometry.lean`.  **Remaining for step 2:**
(i) component connectivity (`IsConnectedPolymer c` for
`c ∈ plaqComponents S` — a reachability-class walk stays in the class
and pulls back through the double subtype `↥c` vs `↥S`; the
`reachable_of_walk_image` pattern); (ii) the reconstruction
(`plaqComponents (⋃ A) = A` for admissible families — the B0a-A3
pointwise-class pattern); (iii) the `sum_nbij'` bijection
`S ↔ admissible families` with values matched by
`integral_prod_prod_plaquetteWeight_of_pairwiseDisjoint`, yielding
`partitionFunction = partition P univ`.

**STEP 2 CLOSED (2026-06-11, commits `23008b4`, `f069760`, `6bba786`;
all oracle-clean `[propext, Classical.choice, Quot.sound]`).**

* (i) `plaqComponents_isConnectedPolymer` (+ packaging
  `plaqComponents_polymer_mem`): a reachability part is
  adjacency-closed (`part_eq_of_mem` + `mem_part_ofSetoid_iff_rel`),
  so the realizing ambient walk pulls back vertex-by-vertex (walk
  induction; the inner `≠` via `Subtype.mk_eq_mk.mp`, NOT
  `congrArg Subtype.val` — the latter pins to the outer subtype).
  Endpoint identification by **subtype eta**: `⟨x.1, h⟩ ≡ x` is
  definitional in Lean 4, so `Reachable.map` along the inline hom
  literal closes by bare `exact`, zero rewriting.
* (ii) `plaqComponents_biUnion_eq` (green on FIRST build): the class
  of any point of a member `c` of a pairwise support-disjoint
  connected family is `c` itself — adjacency cannot leave `c`
  (crossing + `Disjoint.mono_left/right`), and `c`'s own connectivity
  reaches all of it (`Reachable.map`, endpoints by eta).  Plus
  `plaqComponents_disjoint` (set-disjointness via double
  `part_eq_of_mem`).
* (iii) **`partitionFunction_eq_partition`**
  (`L1_GibbsMeasure/PolymerRepresentation.lean`, NEW file):
  `(Z : ℂ) = KP.partition (connectedLatticePolymerSystem μ pe β) univ`
  under `Measurable pe`, `|pe| ≤ B`, the measurable-group instances.
  Route: `partitionFunction_eq_sum_plaquetteSets'` →
  `Finset.sum_nbij'` with `i := componentFamily` (components lifted
  to polymers via **instance-free `Finset.map`**) and `j := union`;
  inverses by `plaqComponents_biUnion` + the reconstruction; values
  by `hfg`-rewrite inside the integral (`prod_biUnion` on
  set-disjoint components), the factorization integral, and
  activity-by-definition (`prod_componentFamily`, per-element `rfl`).
  **Idioms (hard-won):** (a) do NOT use `Finset.image` for the
  polymer lift — the `DecidableEq` elaborated inside the proof
  (`Subtype.instDecidableEq`) differs from the `refine`-time one
  (`Classical.propDecidable`); Decidable instances are DATA, the calc
  link is NOT defeq.  `Finset.map` has no instance argument — seam
  killed.  (b) Pass `i` as a partial application, not a lambda —
  `sum_nbij'` goals then contain no unreduced redexes; `j`-side
  lambda redexes handled by `show`-retyping at bullet starts.  (c)
  The embedding's injectivity hypothesis must be retyped
  `show … from h` before `Subtype.mk_eq_mk` fires (the `.Polymer`
  projection blocks unification).

**Composition DONE (commit `06b032a`, oracle clean):**
**`partitionFunction_eq_exp_clusterSum`** — `(Z : ℂ) =
exp(clusterSum)` for the connected lattice gas under the
volume-uniform KP smallness (constants depend only on `d, B, β, t`);
`partitionFunction_eq_partition` ∘ `partition_eq_exp_clusterSum_of_kp`
∘ `connectedLatticePolymerSystem_kpCriterion_volumeUniform`.  In
particular `Z ≠ 0` at high temperature, volume-uniformly.

**B2 OPENED — the W-campaign (weighted-gas generalization).**  The
reduction: for a multiplicative local observable
`F = ∏_{p∈S_F}(1 + s·g_p)`, `F·∏_p(1+f_p) = ∏_p(1+f̃_p)` with `f̃`
again a LOCAL weight family — so the whole `Z = Ξ = exp(K)` chain must
run for arbitrary local weights `w`, and then `Z·⟨F⟩ = Z[f̃]` is an
instance.  Audit finding: the abstract two-block engine
`integral_mul_of_disjoint_deps` was already weight-general; only the
surfaces were `pe`-specific.  Bricks:

* **W1 CLOSED (commit `ec14d71`, green on FIRST build, oracle
  clean):** `L1_GibbsMeasure/WeightedGas.lean` — `IsLocalWeight`
  (+ `isLocalWeight_plaquetteWeight`), `prod_weight_congr`,
  `integral_prod_weight_mul_of_disjoint`,
  `integral_prod_prod_weight_of_pairwiseDisjoint` (verbatim
  transports), `weightedPartition` `Z[w] = ∫∏(1+w_p)`, binomial
  `prod_one_add_eq_sum`, `integrable_prod_weight` (bounded measurable
  ⇒ integrable; no `MeasurableMul₂`/`MeasurableInv` needed — `w`'s
  measurability is a hypothesis), `weightedPartition_eq_sum`, and the
  Wilson instantiation `weightedPartition_plaquetteWeight`.
* **W2 CLOSED (commit `c1239f8`, green on FIRST build, oracle
  clean):** `weightedLatticePolymerSystem μ w` (same Polymer subtype;
  activity `:= coe ∫∏_{p∈c} w`), `weightedComponentFamily` (+ mem/prod
  lemmas), and **`weightedPartition_eq_partition`**:
  `(Z[w] : ℂ) = KP.partition (weighted gas) univ` for every bounded
  measurable local weight family — verbatim transport of step 2
  (appended to `PolymerRepresentation.lean`).
* **W3 CLOSED (commit `9def5d8`, green on FIRST build, oracle
  clean):** `norm_weightedLatticePolymerSystem_activity_le`
  (`‖z(c)‖ ≤ δ^|c|`),
  `weightedLatticePolymerSystem_kpCriterion_volumeUniform` (verbatim
  transport, `x := δ·e^t`, entropy engine weight-free, `hδ0` carried),
  and **`weightedPartition_eq_exp_clusterSum`**:
  `(Z[w] : ℂ) = exp(clusterSum[w])` under volume-uniform smallness
  with constants depending only on `d, δ, t`.
* **W4a CLOSED (commit `7b49a42`, oracle clean):** the absorption
  identity.  `deformWeight w g T` (`1 + w̃_p = (1+w_p)(1+g_p)` on `T`)
  with closure lemmas (`isLocalWeight_deformWeight`,
  `abs_deformWeight_le` at `δ_w + δ_g + δ_wδ_g`,
  `measurable_deformWeight`) and **`weightedPartition_deform`**:
  `Z[w̃] = ∫ (∏_{p∈T}(1+g_p))·∏_p(1+w_p)` — Gibbs numerators of
  multiplicative observables ARE weighted partition functions, so the
  whole `Z = Ξ = exp(K)` chain applies to them.  (Toolchain rename:
  `abs_add` → `abs_add_le`; and `add_le_add_right`'s explicit-`c`
  form adds on the LEFT in this toolchain — use
  `add_le_add … le_rfl`.)
* **W4b–d (remaining):** (b) the four-gas identity: with
  `T := S_F ∪ S_G` (`S_F, S_G` support-disjoint) and a perturbation
  `g` supported in `T`, `⟨F⟩·Z = Z[deformWeight f g S_F]` etc.
  (from `weightedPartition_deform` + `weightedPartition_plaquetteWeight`),
  hence `⟨FG⟩·Z/(⟨F⟩Z·⟨G⟩Z)·Z = exp(K_{FG}+K−K_F−K_G)` via the four
  `weightedPartition_eq_exp_clusterSum`s (all four gases share the
  SAME Polymer type — only activities differ).  (c) termwise
  cancellation: a tuple `X` whose polymers all miss `S_F` has
  `activity_{FG} = activity_G` and `activity_F = activity_w`
  per-polymer, so `K_{FG}+K−K_F−K_G` is supported on tuples meeting
  BOTH supports — connecting clusters.  **Openers CLOSED (commit
  `a5afb18`, oracle clean):** `deformWeight_union_of_not_mem_left/right`
  (off either region, deforming on the union restricts),
  `weightedLatticePolymerSystem_activity_congr` (off-region agreement
  ⇒ equal activities on region-disjoint polymers), and
  `weightedLatticePolymerSystem_ursell_eq` — the Ursell coefficients
  agree across ALL weighted gases by `rfl` (incomp never touches the
  activity field), so the four cluster sums differ only through
  activity products.  **Tuple-level four-term cancellation CLOSED (commit `a5f82d9`,
  green on first build, oracle clean):** `cluster_term_four_cancel` —
  `ursell·(∏act_{FG} + ∏act_w − ∏act_F − ∏act_G) = 0` on every tuple
  missing either region (activity congruence + `ring`; the cross-gas
  type defeq lets one tuple feed all four activities).  Remaining for
  (c): the tsum-level restriction — `K_{FG}+K−K_F−K_G =` the same
  combination summed over tuples meeting BOTH regions (per-n
  `Finset.sum_filter_of_ne` with the four-term zero, then tsum
  linearity with the four W3 summabilities).  (d) bound the
  surviving sum by the weighted analogue of
  `connecting_cluster_decay` (transport of `connecting_pinned_le_GE`
  + the tilted criterion to the weighted gas) → **B4**: `hIRbound`
  of `lattice_mass_gap_of_clustering_uniform` with
  `covIR t := ⟨FG⟩−⟨F⟩⟨G⟩` at separation `t`.

**Then B2** (the covariance): for plaquette-local multiplicative
observables `F` (deformations `f_p ↦ f_p·(1+s·g_p)` supported on
`S_F`), `⟨F⟩ = Ξ_F/Ξ` (step 2 applied to the deformed gas — SAME
machinery, deformed `pe`), so by `partition_eq_exp_clusterSum_of_kp`:
`⟨FG⟩/⟨F⟩⟨G⟩ = exp(K_{FG} + K − K_F − K_G)`, and the exponent's
cluster sums cancel termwise except on clusters touching BOTH
supports (inclusion–exclusion: the four activities agree on clusters
missing either support).  Bound the surviving sum by
`connecting_cluster_decay`-type estimates → B4: `hIRbound`
discharged with `covIR t := the two-point truncated correlator at
separation t`.

**Everything below the measure-side identification is DONE:**
`Ξ = exp(clusterSum)` ✓, the volume-uniform tail ✓, the connecting
geometry ✓, the composed decay ✓.

   (historical scoping for E4:) regroup Ω by `ν⟨k,f⟩ := ∑(fᵢ+1)`
   (`sigmaFiberEquiv` + `tsum_sigma`; Ω-fibers finite via
   `Fintype.subtype`-style instances — k ≤ N and f bounded), per-N
   finite fiber-sum = the cluster layer of
   `partition_univ_eq_cluster_layers` (the Ω-fiber unpacks to
   `∑_{k ≤ N} (k!)⁻¹·(f-fiber sums)` and the `f ↔ m`-shift bijection
   `mᵢ = fᵢ + 1` via `sum_nbij'` matches the `m`-filter; note
   `a_{fᵢ} = (mᵢ!)⁻¹·W(mᵢ)` definitionally when `a` is instantiated
   at the `clusterSum` terms), tail-kill: layers vanish for
   `N > #Polymer` by `admissible_card_sum_eq` read backwards
   (`tsum_eq_sum`), finish with `partition_univ_eq_sum_card`.
   Final statement: `partition_eq_exp_clusterSum (h : Summable ‖a‖) :
   partition P univ = Complex.exp (clusterSum P)`, then the
   KP-instantiated corollary via `kp_clusterWeight_summable_sharp`
   (norm-comparison `‖aₙ‖ ≤ clusterWeight n` from
   `norm_clusterTerm_le`).

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
