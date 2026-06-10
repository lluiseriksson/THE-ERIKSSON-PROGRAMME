# SHARP-KP-PLAN — the last step to volume-uniform convergence

**Status (2026-06-10):** design document, no code yet.  Written at the close
of the session that proved the volume-uniform KP **criterion**
(`connectedLatticePolymerSystem_kpCriterion_volumeUniform`,
`ConnectedEntropy.lean`).  This plan scopes the one remaining refinement:
the **sharp (weight-respecting) Kotecký–Preiss per-size bound**, which
converts the volume-uniform criterion into volume-uniform **convergence**.

## 1. The gap, precisely

What is proved (all oracle-clean):

* `kp_per_size_bound` (KPBound.lean): under `KPCriterion P a` **and a
  uniform majorant `∀ c, a c ≤ A`**, `clusterWeight P n ≤ (∑‖z‖)·(e·A)ⁿ`.
* `kp_convergence`: absolute convergence of the Mayer series for `e·A < 1`.
* `connectedLatticePolymerSystem_kpCriterion_volumeUniform`: the criterion
  holds for the connected lattice gas with `a(c) = t·|c|` under β-smallness
  depending only on `d`.

The defect: for the lattice gas, `A = t·#P` (the only uniform majorant of
`t·|c|`), so `e·A < 1` is **volume-dependent**.  Sharp KP (Kotecký–Preiss
1986; see Ueltschi, *Cluster expansions: a review*; Friedli–Velenik Ch. 5)
needs no `A`: the criterion alone gives

```
∑_{clusters X pinned at c} (1/n!)|φ(X)| ∏‖z(X_i)‖ ≤ ‖z(c)‖ · e^{a(c)}   (†)
```

and hence `‖clusterSum‖ ≤ ∑_c ‖z(c)‖ e^{a(c)}` — every quantity finite and
volume-uniform per polymer.

## 2. Two proof routes, with a recommendation

### Route A (recommended): Ueltschi-style direct induction — no tree counting

Prove (†) by strong induction on `n` (cluster size), never counting trees
by degree sequence.  Define for each polymer `c` and size bound `n`:

```
T(c, n) := ∑_{m ≤ n} (1/m!) ∑_{X : Fin m → Polymer, incompGraph connected,
                              all X_i incompatible-with-c chain pinned}
            |φ(X)| ∏ ‖z(X_i)‖ e^{...}
```

and show `T(c, n) ≤ a(c)` (or `e^{a(c)} − 1`-form) by: split the cluster at
the polymers directly incompatible with `c` (the "first shell"), apply the
Penrose bound *within shells*, and use the criterion sum
`∑_{c' ≁ c} ‖z(c')‖ e^{a(c')} ≤ a(c)` to absorb each shell.  The induction
hypothesis is applied to the subtrees hanging off the first shell.

Formal advantages: (i) reuses `abs_ursell_le_card_spanningTrees` only
through the **rooted-tree decomposition**, not degree-refined counts;
(ii) the inductive structure mirrors `tree_walk_bound`'s leaf-removal
(precedent in repo); (iii) all sums finite (Fintype) — no convergence
subtleties inside the induction.

Formal challenges: the "split at first shell" partition of connected
clusters pinned at `c` needs a clean combinatorial lemma (cluster =
shell polymers + connected sub-clusters attached to shell elements);
expect Equiv/`Finset.sum_nbij'` work comparable to the Penrose-fiber
session (PenroseFiber.lean, ~5–8 cycles).

### Route B: degree-refined tree counting (Cayley with degrees)

Thread `e^{a}` through `tree_walk_bound` (each vertex `v` accumulates
`a(X_v)^{#children}`), then sum over trees using
`#{trees with degree sequence d_v} = (n−1)!/∏(d_v−1)!` and the exponential
series `∑_k a^k/k! = e^a`.  Mathematically standard, but the degree-refined
Cayley formula is a Prüfer-bijection-level formalization (we deliberately
avoided it once already — the crude `(n+1)^(n+1)` bound sufficed for the
uniform form, but it does NOT suffice here).  Estimate: 10+ cycles, higher
risk.  Choose Route A.

## 3. Statement to aim for (Route A endpoint)

```lean
theorem kp_pinned_cluster_bound (P : PolymerSystem) [Fintype P.Polymer]
    (a : P.Polymer → ℝ) (hcrit : KPCriterion P a) (c : P.Polymer) :
    ∑ n ∈ Finset.range M, ((n+1).factorial : ℝ)⁻¹ *
      ∑ X ∈ {X : Fin (n+1) → P.Polymer | IsCluster ∧ pinned at c},
        |ursell P X| * ∏ i, ‖P.activity (X i)‖ * Real.exp (a (X i))
      ≤ Real.exp (a c) - 1
```

(or the `≤ a c` variant — fix during design; Friedli–Velenik Thm 5.4 uses
`e^a − 1`).  Corollaries: `kp_norm_clusterSum_le_sharp`
(`‖clusterSum‖ ≤ ∑_c ‖z c‖ e^{a c}`), then
**`connectedLatticeClusterSum_summable_volumeUniform`** with NO `hA`
hypothesis — compose with the already-proved volume-uniform criterion.
That closes volume-uniformity entirely.

## 4. After sharp KP (dependency order)

1. Infinite-volume direction: free energy / correlation bounds uniform in N
   (consumes the volume-uniform convergence).
2. Cluster-correlation chain: connect clusterSum derivatives /
   two-point-function expansions to Wilson-loop correlators; discharge the
   IR hypothesis of `lattice_mass_gap_of_clustering_uniform` (M3's
   remaining analytic input besides UV).
3. UV bound (§6.3 of the paper — content not yet in repo).
4. T4 Peter–Weyl / character expansion / area law.

## 5. Campaign state at session close (2026-06-10, verified)

**Landed (oracle-clean, pushed):** `KP/PinnedCluster.lean` —
`pinnedClusterWeight P c n` (pin at coordinate 0), `pinnedClusterWeight_nonneg`,
`clusterWeight_eq_sum_pinned` (exact fiberwise decomposition),
`pinnedClusterWeight_le_clusterWeight`.

**Inputs verified present in the repo** (no work needed):
`IsCluster P X := (incompGraph P X).Connected` (KP/Cluster.lean),
`ursell_eq_zero_of_not_isCluster` (so pinned sums are automatically
supported on genuine clusters), `clusterSum_eq_sum_clusters`
(KP/Expansion.lean), and the Penrose bound `abs_ursell_le_card_spanningTrees`.

**Pinned walk bound — CLOSED (2026-06-10, `KP/PinnedWalk.lean`).**
`tree_walk_bound_pinned`: `∑_{X : X r = x₀} ∏_{v≠r} I(X(p v))(X v)·w(X v)
≤ Aⁿ` — and NOT by reworking the induction: derived from the free
`tree_walk_bound` via the **Option-marker construction** (extend values to
`Option β`; `none` is a synthetic root value of weight `T` interacting like
`x₀` via `I'(none, some y) = I(x₀,y)`, forbidden at non-root vertices via
`I'(·, none) = 0`; the free bound gives `T·Pinned ≤ Aⁿ(T + ∑w)` for all
`T ≥ 0`, and one large `T` forces `Pinned ≤ Aⁿ`).  Oracle clean.  This
trick is reusable wherever a fiber of a free sum is needed.

**Pinned assignment + pinned per-size bound — CLOSED (2026-06-10,
`KP/PinnedBound.lean`).**  `tree_assignment_sum_le_pinned`
(per-tree assignment over the root fiber ≤ `Aᵐ`),
`kp_pinned_per_size_bound` (`pinnedClusterWeight P c n ≤ ‖z c‖·(e·A)ⁿ`),
`pinned_cluster_series_summable`, and **`pinned_cluster_tsum_le`**:
`∑'_n pinnedClusterWeight P c n ≤ ‖z c‖/(1 − e·A)` — the per-polymer
pinned KP bound, uniform-A form.  All oracle-clean.

**The analytic half — CLOSED (2026-06-10, `KP/SharpMajorant.lean`).**
`kpMajorant` (`Φ₀ = 1`, `Φ_{D+1}(c) = exp(∑_{c'≁c} ‖z(c')‖·Φ_D(c'))`),
positivity, depth-monotonicity, and **`kpMajorant_le_exp`**:
`Φ_D(c) ≤ e^{a(c)}` for every depth under the bare KP criterion — the
criterion absorbs one shell per induction step, **no uniform `A`
anywhere**.  This is exactly the analytic engine of FV Thm 5.4.

**Remaining brick — the combinatorial half** (the campaign's last core).
**Detailed design (2026-06-10), so the next session codes, not designs:**

*Objects.*  Work at the level of (rooted labeled tree, assignment) pairs,
never per-tree with degree-refined counting (that route needs
Cayley-with-degrees; rejected).  Define the **depth-`D` rooted tree-sum**

```lean
-- trees on Fin (n+1) rooted at 0, recorded by their parent map
-- (reuse the WalkBound interface: p : Fin (n+1) → Fin (n+1), levels lev)
TreeSum P c D n :=
  (1/n!) · ∑_{(p, lev) admissible, depth ≤ D}
    ∑_{X : Fin (n+1) → Polymer, X 0 = c}
      ∏_{v ≠ 0} 𝟙[P.incomp (X (p v)) (X v)] · ‖z (X v)‖
```

with "admissible" = `p` strictly decreases `lev`, `lev 0 = 0` (each
`(p, lev)` admissible pair corresponds to ≤ one rooted forest; the same
tree appears under several labelings — harmless, this is an upper-bound
route).

*Step C1 (root-deletion graph lemma, standalone, class B).*  In a
connected graph, every connected component of the vertex-deleted subgraph
`G − v₀` contains a neighbor of `v₀`.  Proof: first-exit on a walk to
`v₀` (mirror `exists_adj_crossing_of_walk`).  Needed to know each
child-subtree's root polymer is incompatible with `c`.

*Step C2 (Penrose-tree domination).*  From `abs_ursell_le_card_spanningTrees`
+ `penroseTree`: every pinned cluster `X` contributes
`|φ(X)| ≤ #spanningTrees ≤ ∑_{(p,lev) admissible} ∏_{v≠0} 𝟙[incomp]`
— i.e. `pinnedClusterWeight P c n ≤ TreeSum P c n n` (depth ≤ n always
holds on `n+1` vertices).  Mostly already proved (PinnedBound's `hpen` +
`prod_tree_eq_prod_parents`); repackage with the `(p, lev)` indexing.

*Step C3 (the shell recursion — the real work).*  Prove
`∑_n TreeSum P c D n ≤ Φ_D(c) − 1`-form by induction on `D`:
split `Fin (n+1) \ {0}` by `lev = 1` (the first shell `S`, say `k = |S|`
elements); the remaining vertices organize into subtrees rooted at shell
elements.  The function-space and index bookkeeping:

  - sum over the shell-set `S` (as a `Finset (Fin n)` after relabeling),
    with the multinomial `n! / (k! · ∏ nᵢ!)` emerging from the count of
    labelings — formalize via `Equiv.funSplitAt`-style splitting and
    `Finset.sum_pow`-type identities: the key algebraic lemma is
    `∑_k (1/k!)·(∑_{c'} u(c'))^k = exp(∑ u)` at finite truncation:
    `(∑_{c'} u c')^k = ∑_{f : Fin k → Polymer} ∏ u (f i)` (Fintype.sum_pow,
    exists in Mathlib as `Finset.sum_pow_eq_...` / `Fintype.sum_prod_type`
    iterated — verify name) — ordered k-tuples of children absorb `1/k!`.
  - each child `cᵢ` must satisfy `P.incomp c cᵢ` (𝟙 from its tree edge);
    its subtree contributes a `TreeSum P cᵢ (D−1) nᵢ`-factor.
  - inequality direction is enough everywhere (overcounting allowed:
    different `(S, subtree)` data may produce identical `(p, lev)`).

*Step C4 (endpoint).*  `∑_n pinnedClusterWeight P c n ≤ Φ_n-limit
≤ e^{a(c)}` (`kpMajorant_le_exp`), giving `kp_pinned_cluster_bound` (§3);
compose with `connectedLatticePolymerSystem_kpCriterion_volumeUniform` for
**volume-uniform convergence of the connected lattice gas** — the
campaign's goal.

*Risk register.*  C1 small; C2 medium (re-indexing only); C3 is 4–6 cycles
of `funSplitAt` bookkeeping — the multinomial emergence is the only
genuinely delicate point: do it at the level of ordered tuples (k-tuples of
(child, subtree-size, sub-assignment)) where the factorials are
definitional, and only at the end divide by `n!` using
`Nat.choose`/`Nat.multinomial` identities (`Nat.multinomial` exists in
Mathlib).  Budget total: 6–9 cycles.

*C3 multinomial — RESOLVED DESIGN (2026-06-10, the delicate point made
precise).*  Decomposition map: an admissible `(p, lev, X)` on `Fin (n+1)`
maps to `r := (k, (f_i, m_i, data_i)_{i<k} ordered by increasing shell
roots)`, where the shell roots `s_1 < … < s_k` are the children of `0`
(`parent_eq_zero_iff`), the blocks `V_i` are the `shellRoot` fibers
(`shell_fiber_partition` / `shell_fiber_disjoint`, PROVED), `f_i := X s_i`,
`m_i + 1 := |V_i|`, and `data_i` is the subtree structure relabeled by the
canonical bijection **`s_i ↦ 0`, rest of `V_i` order-embedded into
`{1,…,m_i}`** (the relabeling rule must send the subtree root to `0`; a
plain order isomorphism does not).  Fiber count: LHS data over a fixed `r`
choose disjoint rooted blocks `(V_i, s_i)` with `s_1 < … < s_k`; ordered
rooted-block tuples number `n!/∏ m_i!` (choose the tuple `n!/∏(m_i+1)!`
ways, then a root in each block, `∏(m_i+1)` ways), the roots are distinct
(blocks disjoint), and exactly one of the `k!` orderings is sorted, so

    #fiber(r) ≤ n! / (k! · ∏ m_i!)        (†)

— **exactly** the coefficient pattern of
`∑_k (1/k!) (∑_{c'≁c} w(c')·B_D(c'))^k` after expanding
`B_D(c') = ∑_m (1/m!)·treeSumRaw(c', D, m)`.  Then
`Real.sum_le_exp_of_nonneg` (partial exponential sums) and
`kpMajorant_le_exp` finish.  Remaining formal tasks, in order:
(†) as a standalone counting lemma on sorted rooted-block tuples;
the per-fiber term equality (relabeling transport of the product);
the resummation over `n ≤ N`.

*Dependency check (2026-06-10, verified against the pinned Mathlib):*
`Real.sum_le_exp_of_nonneg : 0 ≤ x → ∑ i ∈ range n, x^i/i! ≤ exp x`
**exists** (`Mathlib/Analysis/Complex/Exponential.lean:244`) — the
endgame's analytic step is free.  `Nat.multinomial` lives in
`Mathlib/Data/Nat/Choose/Multinomial.lean`; a direct
"number of functions with prescribed fiber sizes" lemma was **not**
located — plan (†) via the **coloring view**: ordered disjoint covering
tuples `(V_i)` of sizes `(c_i)` biject with colorings
`χ : Fin n → Fin k` having fiber sizes `(c_i)` (`χ v := the i with
v ∈ V_i`), and the fiber-size count `n!/∏ c_i!` can be proved by
induction on `k` via `Finset.card_eq_sum_card_fiberwise` +
`Nat.choose`-splitting on the last color — or sidestepped entirely by
proving (†) as an *injection* into (permutations of `Fin n`) ×
(per-block local data), where `n!` is `Fintype.card (Equiv.Perm (Fin n))`
and the factorials `∏ m_i!·k!` arise as fiber sizes of the forgetting
map.  Choose at build time; both are 2–3 cycle bricks.

## 6. Honesty invariant (unchanged)

All of this is M3 lattice-side.  None of it reduces M4/M5/Clay
(continuum limit, OS reconstruction, continuum gap — open mathematics).
Distance to Clay: **~0% (<0.1%)**.  Keep it written everywhere.
