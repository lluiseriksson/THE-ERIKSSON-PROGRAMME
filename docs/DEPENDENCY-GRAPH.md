# Dependency graph toward M3 / M4–M5 / Clay — status ledger

**Updated:** 2026-06-09 · **Ground truth:** `lake build YangMillsCore` (8207 jobs green)
+ `#print axioms` (`[propext, Classical.choice, Quot.sound]` on every node marked PROVED).

Classification of every remaining hypothesis:
**A** = known published mathematics, formalizable now ·
**B** = standard mathematics missing from Mathlib (infrastructure) ·
**C** = genuinely open/original mathematics ·
**D** = repo plumbing / API.

Honest headline: **all machine-checked progress is lattice/finite-volume (M3-side).
Distance to Clay remains ~0% (<0.1%)** — M4/M5 (continuum limit + OS/Wightman
reconstruction + continuum gap) are class C and untouched by everything below.

---

## 1. The M3 chain (strong-coupling lattice mass gap — Osterwalder–Seiler 1978, class A)

```
M3: unconditional lattice mass gap at strong coupling
 └─ lattice_mass_gap_of_clustering_uniform          PROVED (conditional form)
     ├─ UV suppression hypothesis (§6.3)            OPEN  [A: single-scale bound]
     └─ IR geometric cluster bound                  OPEN  [A; reduces to KP ↓]
         └─ kp_per_size_bound                      **PROVED 2026-06-10 — TARGET B CLOSED**
             clusterWeight P n ≤ (∑‖z‖)·(e·A)ⁿ under KPCriterion with a ≤ A
             (KPBound.lean); corollaries kp_convergence (absolute summability
             of the Mayer series) and kp_norm_clusterSum_le
             (‖clusterSum‖ ≤ (∑‖z‖)/(1−e·A)) for e·A < 1.
             Honest note: uses the UNIFORM smallness e·max(a) < 1 — slightly
             stronger than the sharp KP criterion; refinable later without
             touching the architecture.  Structure of the proof:
             ├─ clusterWeight glue to clusterSum    PROVED (ClusterWeight.lean)
             │    norm_clusterTerm_le, clusterSum_summable_of_geometric,
             │    norm_clusterSum_le (‖Ξ-log-series‖ ≤ C/(1−r))
             ├─ (i) PENROSE TREE-GRAPH INEQUALITY   **PROVED 2026-06-09**
             │    abs_ursell_le_card_spanningTrees
             │    |φ(X)| ≤ #spanningTrees(incompGraph P X)
             │    [Penrose 1967; partition scheme + greedy BFS, see §3]
             ├─ uniform Penrose bound               **PROVED 2026-06-09**
             │    abs_ursell_le_treeCount: |φ(X)| ≤ treeCount n,
             │    X-independent majorant (treeCount = all labeled trees on Fin n)
             ├─ (ii) per-tree activity walk         **PROVED 2026-06-10**
             │    tree_walk_bound (WalkBound.lean): abstract leaf-removal
             │    induction over shrinking vertex types (funSplitAt);
             │    ∑_X ∏_{v≠r} I(X_{p v},X_v)·w(X_v)·w(X_r) ≤ Aⁿ·∑w under
             │    the conditional neighbour bound ∑_y I x y·w y ≤ A.
             │    All three steps (i)+(ii)+(iii) of the per-size estimate
             │    are now proved.  Assembly [D] half done (2026-06-10):
             │    **tree_assignment_sum_le PROVED** (KPBound.lean) — the
             │    walk instantiated at the polymer objects:
             │    ∑_X (∏_{e∈T} 𝟙[e ∈ incompEdges X])·∏‖z‖ ≤ Aᵐ·∑‖z‖ under
             │    KPCriterion with a ≤ A.  Remaining assembly (final [D]):
             │    expand |φ(X)| ≤ #spanningTrees as ∑_{T∈shapes} edge-
             │    indicator products (𝟙[∀e∈T,…] ≤ ∏ pointwise by_cases),
             │    Finset.sum_comm, apply tree_assignment_sum_le per T,
             │    count shapes by treeCount_le_pow, divide by (n+1)! via
             │    succ_pow_le_exp_mul_factorial ⇒ kp_per_size_bound:
             │    clusterWeight P n ≤ (∑‖z‖)·(e·A)ⁿ ⇒ Target B closes.
             ├─ (iii) tree counting                 **PROVED 2026-06-09**
             │    treeCount_le_pow: treeCount (m+1) ≤ (m+1)^(m+1), via the
             │    parent-function injection (trees recoverable from their
             │    greedy parent map — no Prüfer needed); with the proved
             │    (n+1)ⁿ ≤ eⁿ·n! this is exactly the needed order.
             │    Closed numerical Penrose bound: abs_ursell_le_succ_pow
             │    |φ(X)| ≤ (m+1)^(m+1).
             └─ assembly of (i)+(ii)+(iii)          OPEN  [D]
 └─ polymer representation: lattice Gibbs correlators ⇄ polymer system
    satisfying KPCriterion at strong coupling        OPEN  [A: large formalization;
    the bridge that makes the KP output speak about Wilson/gauge observables]
 └─ (Wilson-loop variant) T4: Peter–Weyl/characters  OPEN  [B: major]
```

Mayer/Ursell layer feeding the above — **all PROVED, unconditional:**
`ursellComplete_recurrence` (T1, d(n+1) = −n·d(n)), `ursellComplete_eq`
(φ(K_{n+1}) = (−1)ⁿ·n!), `clusterSum_singlePolymer_eq_log`,
`partition_singlePolymer_eq_exp` (n=1 Mayer identity Ξ = exp(clusterSum)).

## 2. M4/M5 and Clay (class C — open mathematics)

Continuum limit of 4D non-abelian lattice YM, OS axioms (esp. OS1/O(4)),
Wightman reconstruction, continuum mass gap: **no published proof exists for
the non-abelian case.  Nothing here can be formalized until it exists on
paper.** No node below the M3 line reduces any Clay-side obstruction.

## 3. What was machine-checked for the Penrose theorem (plain language)

The Ursell coefficient φ(X) is an alternating sum over all connected
subgraphs of the incompatibility graph; naively it could be huge.  Penrose's
1967 theorem says the cancellations are so strong that |φ| is bounded by the
number of spanning trees.  The verified proof: fiber the connected subgraphs
over their greedy BFS tree (`penroseTree`, least-parent rule); each fiber is
a Boolean interval `[T, penroseEnvelope H T]` (`penrose_hfiber`), and an
alternating sum over a Boolean interval collapses to ±1 or 0
(`interval_signed_sum`).  Supporting facts proved on the way: paths in trees
realize distances, adjacent tree vertices sit on consecutive levels, BFS
levels and greedy parents are frozen on each interval, π fixes spanning
trees, π(E) is itself a spanning tree (`hmaps`).

Oracle on the headline (2026-06-09):
`'YangMills.KP.abs_ursell_le_card_spanningTrees' depends on axioms:
[propext, Classical.choice, Quot.sound]`.

## 4. Next best targets (dependency order, expected difficulty)

1. **(ii) per-tree activity walk** [A, medium]: for a fixed spanning tree on
   `Fin (n+1)`, bound `∑_X ∏_{edges} 𝟙[incomp] ∏‖z‖` by leaf-removal
   induction using `kp_neighbor_sum_le`.  Needs a "tree has a leaf" lemma
   (degree-1 vertex) — check Mathlib; small if present.
2. **(iii) Cayley/Prüfer counting** [B, medium-large]: `#spanningTrees(G on
   Fin (n+1)) ≤ (n+1)^(n−1)`.  Injectivity of a Prüfer-type encoding
   suffices (no need for the exact bijection).  Mathlib-worthy.
3. **kp_per_size_bound assembly** [D→A, small once 1+2 land].
4. **Polymer representation of the strong-coupling lattice expansion**
   [A, large]: the genuinely physical step tying KP to `GibbsMeasure`.
5. **T3 (LG6 centre invariance)** [D/A, small-medium]: independent thread,
   Wilson-loop selection rule.
6. **T4 Peter–Weyl/area law** [B, major]: only needed for the Wilson-loop
   form of M3.

Honesty invariant: closing 1–6 completes **M3 (lattice)**.  It does not move
Clay, whose obstruction is item §2 — and saying otherwise is the one failure
mode this repo is built to prevent.
