# Handoff — Kotecký–Preiss cluster expansion (Targets A & B)

**Date:** 2026-05-30 · **Status:** both heavy targets reduced to one lemma each,
everything else verified and oracle-clean (`[propext, Classical.choice, Quot.sound]`),
wired into `YangMillsCore` (full build: 8194 jobs green). No `sorry`, no project axioms.

This document is the single entry point for whoever (human in interactive Lean, or a
stronger prover) closes the two remaining lemmas. It assumes the discipline of
`FOUNDATIONS.md`: imported hard inputs are carried as **explicit hypotheses**, never as
axioms; nothing with a `sorry` enters `YangMillsCore`.

---

## The big picture

The Mayer/Kotecký–Preiss cluster expansion underlies §5 (terminal clustering) and §6.2
of the Eriksson paper, with endpoint Appendix A (KP bound ⇒ exponential decay of
truncated correlations ⇒ the mass-gap rate `m*` fed to `mass_gap_bound`, §7).

It splits into two independent heavy results, each now **one lemma away** from done:

| Target | Statement | Remaining lemma | Obstacle |
|---|---|---|---|
| **A** | `φ(K_{k+1}) = (−1)^k·k!` (Ursell value on complete graphs) | `ursellComplete_recurrence` | component-of-vertex-0 bijection on `Finset` subgraphs |
| **B** | KP convergence of the cluster sum under the smallness criterion | `kp_per_size_bound` | Penrose tree-graph inequality (spanning-tree enumeration) |

Both remaining lemmas are large `Finset`/graph constructions that need **interactive
Lean** (inspecting intermediate goals), which is why they were not closed in the
paste-only loop that produced everything else.

---

## Target A — `ursellComplete_recurrence` — **CLOSED (2026-06-09)**

> **STATUS: DONE.** Proved unconditionally in `YangMills/KP/UrsellRecurrence.lean`
> (wired into `YangMillsCore`; oracle `[propext, Classical.choice, Quot.sound]`).
> The closed form `ursellComplete_eq` and the single-polymer Mayer identity
> (`clusterSum_singlePolymer_eq_log`, `partition_singlePolymer_eq_exp`) are now
> hypothesis-free.  The section below is kept as the historical blueprint;
> the implemented proof follows skeleton steps 1–5 with `reachSet` (the
> Finset of vertices reachable from 0) in place of `ConnectedComponent.supp`,
> a sign-reversing edge-toggle involution (`Finset.sum_involution`) for the
> small fibers, and `Fin.succAbove`-relabeling (`Finset.subset_image_iff` +
> `Finset.sum_image`) for the codimension-one fibers.  **Only Target B remains.**

**File:** `YangMills/KP/Ursell.lean`. **Goal to prove:**

```lean
theorem ursellComplete_recurrence (n : ℕ) (hn : 1 ≤ n) :
    ursellComplete (n + 1) = -(n : ℤ) * ursellComplete n
```

Closing this makes `ursellComplete_closed_form` **unconditional** (it currently takes
the recurrence as hypothesis), giving Target A in full.

### Already verified and available (same file)
- `ursell` — the Ursell/Mayer coefficient (signed sum over connected spanning subgraphs).
- `ursell_fin_one/two/three` — `φ = +1, −1, +2` (data points; confirm the pattern).
- `ursell_eq_zero_of_not_isCluster` — non-clusters contribute 0.
- `completeSystem`, `ursellComplete` — `d(n) = φ(K_n)` as a concrete `ℕ → ℤ`.
- `ursellComplete_one/two/three` — `d = 1, −1, 2` on the canonical system.
- `closed_form_of_recurrence` — **recurrence ⟹ `(−1)^k·k!`** (the back-half, done).
- `allSubgraphs_signedSum` — `∑_{E ⊆ E(K_n)} (−1)^{|E|} = [n ≤ 1]` (the `a(n)` ingredient).
- `componentSupp_closed_under_adj` — **no edge leaves a connected component** (the
  partition fact that makes the fiber split clean).

### Proof skeleton (5 steps; see `kp-cluster-expansion-plan.md` for the long form)
1. Fiber the full signed sum over all subgraphs of `K_{n+1}` by the connected component
   `S` of vertex 0 (`Finset.sum_fiberwise`, key `componentSupp_closed_under_adj`).
2. Each fiber `{E : comp₀ = S}` splits as `{connected spanning of K_S} × {arbitrary of
   K_{Sᶜ}}` with `|E| = |E_S| + |E_c|`; fiber sum `= d(|S|)·a(n+1−|S|)`.
3. `allSubgraphs_signedSum`: `a(m) = [m≤1]`, so only `|S| ∈ {n, n+1}` survive.
4. `|S|=n+1` ⟹ `d(n+1)`; `|S|=n` ⟹ `n` choices, each `d(n)`. Sum `= 0` (since `n+1≥2`).
5. `0 = d(n+1) + n·d(n)` ⟹ the recurrence.

**Mathlib API ready:** `SimpleGraph.ConnectedComponent.supp`, `mem_supp_congr_adj`,
`connected_toSimpleGraph`, `maximal_connected_induce_supp`, `Finset.sum_fiberwise`,
`Finset.sum_nbij'`, `Finset.sum_powerset_neg_one_pow_card`.

**Hard part:** step 2 as a `Finset.sum_nbij'` between a filtered powerset and a product
of two filtered powersets, with the cardinality split. This is the focused interactive
session.

**Bonus already in place (fully assembled):** the *single-polymer case of the Mayer
identity* is a complete theorem **conditional on Target A**, in
`YangMills/KP/SinglePolymer.lean`:
- `clusterSum_singlePolymer` : `clusterSum (singlePolymerSystem z) = Complex.log (1+z)`.
- `partition_eq_exp_clusterSum_singlePolymer` :
  `Ξ(singlePolymerSystem z) = Complex.exp (clusterSum …)` (for `‖z‖<1`).

Both take only `hrec` (Target A's recurrence) as hypothesis. So the *moment*
`ursellComplete_recurrence` is closed, the n=1 case of `Ξ = exp(clusterSum)` becomes
**unconditional with zero extra work** — discharge `hrec` and done. The assembly already
composes `ursellComplete_closed_form` + `mayer_log_series_complex` + factorial
cancellation + `partition_singleton` + `Complex.exp_log`, all verified.

---

## Target B — `kp_per_size_bound` — **CLOSED (2026-06-10)**

> **STATUS: DONE.**  The full chain is proved and oracle-clean in
> `YangMillsCore` (see `docs/DEPENDENCY-GRAPH.md` for the graph):
> * `abs_ursell_le_card_spanningTrees` — **Penrose 1967 tree-graph
>   inequality**, via the verified partition scheme (`PenroseScheme.lean`)
>   instantiated with the greedy BFS scheme (`PenroseBFS.lean`,
>   `PenroseFiber.lean`: `hmaps` + `hfiber` both discharged);
> * `treeCount_le_pow` — tree counting at Cayley order via the
>   parent-function injection (no Prüfer needed);
> * `tree_walk_bound` — the per-tree activity walk (`WalkBound.lean`,
>   abstract leaf-removal induction over shrinking vertex types);
> * `tree_assignment_sum_le` — the walk instantiated at the polymer
>   objects under `KPCriterion` (`KPBound.lean`);
> * **`kp_per_size_bound`** — `clusterWeight P n ≤ (∑‖z‖)·(e·A)ⁿ`;
> * **`kp_convergence`**, **`kp_norm_clusterSum_le`** — absolute
>   convergence of the Mayer series and `‖clusterSum‖ ≤ (∑‖z‖)/(1−e·A)`
>   for `e·A < 1`.
>
> Honest caveat: uniform smallness `e·max(a) < 1` (slightly stronger than
> the sharp KP criterion; refinable without architectural change).
> Both heavy targets of this handoff (A and B) are now closed.  The
> remaining lattice work toward M3 is the polymer representation
> (lattice Gibbs ⇄ polymer system) and the UV bound.  Historical
> blueprint below.

> **UPDATE (2026-06-09): front glue DONE — open content now precisely stated.**
> `YangMills/KP/ClusterWeight.lean` (in `YangMillsCore`, oracle-clean) defines the
> concrete per-size weight
> `clusterWeight P n = (1/(n+1)!)·∑_X |φ(X)|·∏‖z(Xᵢ)‖`
> and proves `norm_clusterTerm_le`, `clusterSum_summable_of_geometric`, and
> `norm_clusterSum_le` (`‖clusterSum P‖ ≤ C/(1−r)`).  So the abstract back-half is now
> wired to the actual Mayer object, and **Target B is exactly one estimate**:
>
> ```lean
> KPCriterion P a → ∃ C r, 0 ≤ r ∧ r < 1 ∧ ∀ n, clusterWeight P n ≤ C * r ^ n
> ```
>
> The open mathematics behind it: (i) Penrose tree-graph inequality
> `|ursell P X| ≤ #(spanning trees of incompGraph P X)`; (ii) per-tree activity sum
> bound by walking edges with `kp_neighbor_sum_le`; (iii) Cayley-order tree counting
> `≤ n^{n−2}` with `n^{n−2}/n! ≤ eⁿ` (crude binomial counting of `(n−1)`-edge subsets
> is *insufficient* — it loses the geometric decay).  None of these are in Mathlib.
>
> **Progress on (i) and (iii) (2026-06-09):**
> * `PenrosePrep.lean` — `spanningTrees` defined (so (i) is statable verbatim);
>   step (iii)'s analytic half `(n+1)ⁿ ≤ eⁿ·n!` **proved**
>   (`succ_pow_le_exp_mul_factorial`).
> * `PenroseScheme.lean` — the **partition-scheme mechanism of (i) proved**:
>   `interval_signed_sum` (Boolean-interval signed sum `= (−1)^{|T|}·[R = T]`) and
>   `abs_signedSum_le_of_scheme` (fibers-are-intervals ⟹ `|signed sum| ≤ #Tr`),
>   assembled into `abs_ursell_le_card_spanningTrees_of_scheme`.  What remains of
>   (i) is the **concrete BFS/Penrose scheme**: construct `π` (greedy spanning tree
>   of a connected subgraph) and envelope `R`, and verify `hmaps`/`hfiber`
>   (each fiber is exactly the interval `[T, R T]`).  All oracle-clean, in core.
> **STEP (i) CLOSED (2026-06-09): the Penrose tree-graph inequality is
> UNCONDITIONAL.**  `PenroseFiber.lean` proves `penrose_hfiber` (the fiber
> over a spanning tree `T` is exactly the interval `[T, penroseEnvelope H T]`)
> and the headline `abs_ursell_le_card_spanningTrees`:
> `|ursell P X| ≤ #spanningTrees(incompGraph P X)` — Penrose 1967, no
> hypotheses, oracle `[propext, Classical.choice, Quot.sound]`.
> Remaining for `kp_per_size_bound`: (ii) the per-tree activity walk and
> (iii) Cayley/Prüfer tree counting.  See `docs/DEPENDENCY-GRAPH.md`.
>
> * `PenroseBFS.lean` — the **concrete greedy BFS scheme constructed, `hmaps`
>   DISCHARGED**: `bfsLevel`/`bfsParent`/`penroseTree`/`penroseEnvelope` defined;
>   proved: `exists_bfs_parent`, `dist_le_succ_of_adj`, `bfsParent_spec`/`_min`,
>   `penroseTree_subset` (`π(E) ⊆ E`), `penroseTree_connected`,
>   `penroseTree_card` (`m` edges), `penroseTree_isTree`, and
>   **`penroseTree_mem_spanningTrees`** — exactly `hmaps` of the scheme theorem.
>   **The single remaining lemma of step (i) is `hfiber`**: for a spanning tree
>   `T` of `H`, and any `E` supported on `H`-edges,
>   `(E connected ∧ penroseTree E = T) ↔ (T ⊆ E ∧ E ⊆ penroseEnvelope H T)`.
>   Proof route (classical Penrose): `⟸` — edges within `penroseEnvelope` keep
>   all levels (`bfsLevel E = bfsLevel T`, by `dist_le_succ_of_adj` induction up
>   the levels) and the greedy parent choice is unaffected (admissible
>   same-level / later-choice edges are never selected, `bfsParent_min`);
>   `⟹` — every `E`-edge connects levels differing by ≤ 1
>   (`dist_le_succ_of_adj`), and a lower endpoint below the greedy parent would
>   contradict `penroseTree E = T` (it would *be* the parent).  All ingredients
>   are in `PenroseBFS.lean`; this is one focused session of level bookkeeping.

**File:** `YangMills/KP/Convergence.lean` (back-half) + `Criterion.lean` (setup).
**Goal to prove** (schematic — the per-size cluster weight obeys a geometric bound):

```lean
theorem kp_per_size_bound [Fintype P.Polymer] {a : P.Polymer → ℝ}
    (h : KPCriterion P a) (X : P.Polymer) (n : ℕ) :
    (size-n cluster weight containing X) ≤ a X * r ^ n      -- some 0 ≤ r < 1
```

Feeding its conclusion into the verified back-half closes Target B:
- `cluster_series_summable` — geometric per-size bound ⟹ `Summable`.
- `cluster_sum_le` — … ⟹ `∑' ≤ C/(1−r)` (the explicit convergence bound).

### Already verified and available
- `KPCriterion` — the smallness condition (`Criterion.lean`).
- `kp_activity_le` — `‖z(X)‖ ≤ a(X)` (induction seed).
- `kp_neighbor_sum_le` — `∑_{Y incomp X} ‖z(Y)‖ ≤ a(X)` (the tempered neighbour bound,
  the per-edge step of the tree sum).
- `cluster_series_summable`, `cluster_sum_le` — the back-half (done, wired to root).

### Proof route (the open content = Penrose tree-graph inequality)
1. Bound `‖ursell(Y)‖` of an `n`-cluster by its number of spanning trees (Cayley-type
   `n^{n-2}` bound) times a per-tree weight.
2. Sum the per-tree weight by walking each tree edge and applying `kp_neighbor_sum_le`
   (strong induction on `n`); the factorial from tree-counting cancels against `1/n!`.

**Mathlib API ready:** `SimpleGraph.IsTree`, `IsAcyclic`, `IsTree.card_edgeFinset`
(tree on `m` vertices has `m−1` edges), `Connected.exists_isTree_le_of_le_of_isAcyclic`
(spanning tree exists), `isTree_iff_minimal_connected`.

**Hard part:** the spanning-tree enumeration and the inductive weight sum. No
spanning-tree *counting* (Cayley) is in Mathlib as of 2026-05; that sub-result may need
its own development.

---

## How to verify after editing

```powershell
cd <repo>
lake build YangMillsCore
"import YangMillsCore`n#print axioms YangMills.KP.<lemma>" | Set-Content _oc.lean
lake env lean _oc.lean; Remove-Item _oc.lean
```

Expected oracle on every declaration: `[propext, Classical.choice, Quot.sound]`
(some pure-induction lemmas are even cleaner: `[propext, Quot.sound]`). Any other axiom
— especially a project-local one — means the discipline was broken; revert.
