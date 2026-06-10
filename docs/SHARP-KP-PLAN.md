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

## 5. Honesty invariant (unchanged)

All of this is M3 lattice-side.  None of it reduces M4/M5/Clay
(continuum limit, OS reconstruction, continuum gap — open mathematics).
Distance to Clay: **~0% (<0.1%)**.  Keep it written everywhere.
