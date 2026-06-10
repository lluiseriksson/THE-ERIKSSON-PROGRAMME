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

*C3 multinomial — **DESIGN CORRECTION (2026-06-10, late)**, supersedes the
sorted-roots count above.*  The bound `#fiber(r) ≤ n!/(k!·∏ m_i!)` for a
**fixed** component tuple `r` (hence fixed size-vector `m`) is **FALSE in
general**: the `k!` orderings of an unordered block family have *permuted*
size-vectors, so the `1/k!` saving cannot be claimed per fixed `m` —
do not build that lemma.  Correct architecture:

1. **Do not sort.**  Decompose pairs `(LHS datum, σ)` where `σ` orders the
   shell: each LHS datum appears exactly `k!` times, giving
   `∑_{LHS, shell size k} term = (1/k!)·∑_{(datum, σ)} term` — the `1/k!`
   enters here, exactly (shell roots are distinct, so all `k!` orderings
   are distinct).
2. `(datum, σ) ↦ r` (unsorted component tuple).  Fiber bound per `r`, now
   with NO `k!`:  `#fiber(r) ≤ n!/∏ m_i!`  (†′) — ordered rooted-block
   tuples with sizes `m_i + 1`.
3. **(†′) multiplicatively via a permutation injection** (no division, no
   `Nat` subtleties): construct an injection
   `D′(m) × (Π i, Equiv.Perm (Fin (m_i))) ↪ (Fin n ≃ Fin n)` —
   concatenate the blocks in tuple order, each block listed root-first
   and then its remaining elements through `Finset.orderEmbOfFin`
   composed with the local permutation; `finSigmaFinEquiv`-style index
   arithmetic splits `Fin n` by the size vector.  Injectivity: with `m`
   fixed, the positions determine the blocks and roots, and
   `orderEmbOfFin` is injective, so local permutations are recovered.
   Then `card D′(m) · ∏ m_i! ≤ n!` since `card (Fin n ≃ Fin n) = n!`.
4. Resummation unchanged: `(1/k!)·∑_r (n!/∏ m_i!)·term(r)` recombines to
   `∑_k (1/k!)(∑ w·B_D)^k ≤ exp(...)` by `Real.sum_le_exp_of_nonneg`.

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

## 5b. C3 construction inventory (2026-06-10, end of session — ALL LOCAL
INGREDIENTS PROVED, oracle clean)

In `KP/SharpShell.lean`: C1 (`exists_adj_reachable_in_deleted`),
`connected_dist_lt_card`, `IsAdmissible` (exact increments), `treeSumRaw`
(+ nonneg, depth-mono, base cases `= 1` and `= 0` matching `kpMajorant`),
C2 (`pinnedClusterWeight_le_treeSumRaw`), the shell-root calculus
(`shellRoot` + 9 lemmas), the fiber partition
(`shell_fiber_partition`/`_disjoint`), **the counting bound**
(`card_blockData_mul_le`, via `placeFun` and the permutation injection),
the marked enumeration (`markedEmb`/`markedEquiv` APIs), **the descent**
(`subtreeStructure_isAdmissible` — shell subtrees of depth-(D+1)
structures are admissible depth-D structures), and **the term transport**
(`subtreeParent_apply_val`, `prod_filter_ne_zero_eq`,
`subtree_prod_transport`).

**The single remaining lemma — the master assembly:** for each `n`,
decompose `treeSumRaw P c (D+1) n`'s sum over `(p, lev, X)` along
(shell-ordering pairs ↦ block data + relabeled components); the fiber is
priced by `card_blockData_mul_le`, the terms by `subtree_prod_transport`
+ `shell_fiber_partition` (+ `Finset.prod_biUnion` and
`Finset.mul_prod_erase` at `v = s` where `parent_eq_zero_iff` turns the
root edge into `𝟙[incomp c ·]`), and the resummation over `n ≤ N`
recombines via the multinomial coefficients into
`∑_k (1/k!)(∑_{c'≁c} w(c')·B_D(c'))^k ≤ exp(...) = Φ_{D+1}(c)`
(`Real.sum_le_exp_of_nonneg`).  One theorem, ~300 lines, every
ingredient on the shelf.  Endpoint: §3's `kp_pinned_cluster_bound`, then
volume-uniform convergence by composition (§5, C4).

## 5c. The master assembly — final blueprint (2026-06-10, late session;
includes TWO design corrections caught by adversarial review)

**Corrections already applied in code:** (i) the per-fixed-`m` sorted
count is false — `1/k!` enters via `(datum, σ)`-pairs (§ above); (ii)
`p(0)` was unconstrained, so `treeSumRaw` overcounted each tree `n+1`
times — fixed by root canonicity `p 0 = 0` in the filter (with
`bfsParent_zero` keeping C2 green).  **Do not undo either.**

**The sum chain, exactly:**

1. *k-partition:* split the canonical-admissible `(p,lev)`-sum by
   `k := (univ.filter (fun s => s ≠ 0 ∧ p s = 0)).card` (the shell size);
   `n ≥ 1 ⇒ k ≥ 1`.
2. *Symmetrization:* per class, `∑_{(p,lev)} F = (1/k!)·∑_{(p,lev,σ)} F`
   where `σ : Fin k ≃ shell-subtype`; `#σ = k!` by `Fintype.card_equiv`.
3. *The injection (the only remaining hard step):*
   `(p, lev, σ, X) ↦ (ρ, comps)` where `ρ := shell_blockData`-data
   (PROVED to be `IsBlockData (univ.erase 0)`) and
   `comps i := (subtreeParent …, subtreeLev …, X ∘ markedEmb_i)` — each
   canonical-admissible at depth `D` (PROVED: `subtreeStructure_isAdmissible`;
   canonicity `subtreeParent 0 = 0` is definitional).  Term preservation:
   `master_partition` + `subtree_prod_transport` +
   `subtreeParent_apply_val` (ALL PROVED).  Injectivity: reconstruction —
   `p`/`lev`/`X` are determined by `(ρ, comps)` (recovery pattern as in
   `placeFun_injective`/`card_blockData_mul_le`'s `hblock`).
4. *Pricing:* for fixed `(k, m, comps)`, the `ρ`-sum contributes
   `#blockdata(m) ≤ n!/∏ m_i!` (`card_blockData_mul_le` at
   `U := univ.erase 0`, `U.card = n`).
5. *Per-block identification:* the comps-sum factorizes; each block's sum
   is exactly `∑_{c' ≁ c} ‖z c'‖ · treeSumRaw P c' D (m i)` (root-edge
   factor `𝟙[incomp c (X'_i 0)]·w(X'_i 0)` + inner = `treeSumRaw`'s
   summand).
6. *Resummation:* `(1/n!)·tSR(c,D+1,n) ≤ ∑_k (1/k!) ∑_{m} ∏ (S(m_i)/m_i!)`
   with `S(m) := ∑_{c'≁c} w c'·tSR(c',D,m)`; sum over `n ≤ N`, expand the
   power by `Finset.prod_univ_sum` (products of sums = sums over
   `Fintype.piFinset`), bound by
   `∑_k (1/k!)(∑_{c'≁c} w c' · B_D(c'))^k ≤ exp(…) = Φ_{D+1}(c)`
   via `Real.sum_le_exp_of_nonneg` and (inductively) `B_D ≤ Φ_D` from
   `kpMajorant_le_exp`-side composition.

Everything in 1, 2, 4, 5, 6 is glue over proved lemmas; step 3's
reconstruction is the one genuinely laborious proof left (≈200 lines,
twice-precedented pattern).

*Splice architecture — REFINED (2026-06-10, last; eliminates dependent
pi-Finsets).*  Do NOT build the target index as a sigma over block data of
dependent component tuples.  Instead, after symmetrization
(`sum_symmetrize`, PROVED) and the k-partition:

  - **S1 (group by block data):** fiberwise over
    `(pl, σ) ↦ ρ(pl,σ) := fun i => (shellFiber pl (σ i).1, (σ i).1)`
    (lands in `IsBlockData (univ.erase 0)` — `shell_blockData`, PROVED).
    Recovery equations (`parent_recovery(_root)`, `lev_recovery`, PROVED)
    show consistency determines `(p, lev)` from per-block data.
  - **S2 (factorize the consistent sum):** for FIXED `ρ`, the sum over
    consistent `(p, lev, X)` factorizes across fibers — the function
    spaces split along the (fixed!) fiber partition, so the splitting
    equivalence is non-dependent.  Output shape: per-block sums over
    block-local structure/assignment functions.
  - **S3 (block-local identification):** per block `(V, s)` with
    `(V.erase s).card = m`, transport the block-local sum along
    `markedEquiv` (function-space congruence, `Equiv.arrowCongr`-style):
    block-local sum `= ∑_{c'≁c} ‖z c'‖ · treeSumRaw P c' D m`
    (the root-edge factor at `s` plus `subtree_prod_transport`).
  - **S4 (pricing and resummation):** fiberwise over the size vector `m`,
    `#blockdata(m) ≤ n!/∏ m_i!` (`card_blockData_mul_le`), then step 6
    unchanged.

S2 and S3 are each single-lemma bricks against fixed data; S1 is
`Finset.sum_fiberwise_of_maps_to`; S4 is proved.  The dependent-type
hazard of the original step-3 formulation is gone.

*S2+S3 FUSED (2026-06-10, final refinement).*  Do not give block-local
conditions an independent axiomatization (that would need the unproved
gluing direction).  Instead **define** each block factor as the relabeled
canonical sum itself:
`G_i(h) := Σ-shape over canonical depth-D structures on Fin (m_i + 1)` —
then S3 is a free `Equiv.sum_comp` along `markedEquiv`-`arrowCongr`, and
the entire S2+S3 content is ONE inequality per fixed `ρ`:

    ∑_{(pl, σ, X) : consistent with ρ, X 0 = c} term(pl, X)
      ≤ ∏_i ∑_{c'} 𝟙[P.incomp c c']·‖z c'‖·(treeSumRaw-inner P c' D (m i))

proved by: term factorization (`master_partition` +
`subtree_prod_transport`, PROVED), per-block canonicity of the image
(`subtreeStructure_isAdmissible` + `subtreeParent 0 = 0`, PROVED),
injectivity of the decomposition (recovery equations, PROVED), and the
product-of-sums engine (`sum_coverSplit`/direct pi-expansion, PROVED).
Budget: ~150–200 lines, all ingredients on the shelf; the only new
content is the bookkeeping of the injection into the Π-of-triples target
(non-dependent for fixed `ρ`).  After it: the final chain (k-partition,
`sum_symmetrize`, fiberwise-`ρ`, `card_blockData_mul_le`, resummation)
is arithmetic.

## 5d. X-sum weave — attempt log (2026-06-10, two attempts, both cleanly
discarded; repo green throughout)

Attempt 1 failure: `set`-bound dependent per-block functional → motive
errors.  Fix applied and COMMITTED: `blockFunctional` as a top-level def
+ `sum_blockFunctional` (rfl-level repackaging of `block_sum_eq` — the
shapes match exactly).

Attempt 2 failure (with the named functional): motive-incorrect rewrite
in the first calc step.  Attempt 3 (same session) made REAL PROGRESS:
**the `Eq.trans`-with-term-application pattern WORKS** — both
`(master_factorization_fn …).trans ?_` and `(sum_pinned_eq …).trans ?_`
elaborate cleanly (defeq absorbs the beta-mismatch; no motives).  The
surviving failure is isolated to ONE spot: the root-factor conversion
after `unfold blockFunctional; congr 1` — the
`rw [markedEmb_zero, hX0]` is motive-incorrect even after `dsimp only`
(a dependent occurrence of `markedEmb … 0` survives, likely inside an
implicit/proof position the goal display hides).  **Prescription:** do
not convert the root factor by rewriting in place.  State it as a
standalone two-sided `have`:
`have hroot : (if P.incomp (X 0) (X (σ i)) then (1:ℝ) else 0) * ‖…(X (σ i))‖
  = (if P.incomp c (X (markedEmb (shellFiber p lev (σ i)) (σ i) rfl 0))
     then (1:ℝ) else 0) * ‖…‖ := by
  rw [markedEmb_zero]; rw [(Finset.mem_filter.mp hX).2]`
(isolated goal, both sides explicit, no dependent context) — then close
the factor-equality with `exact hroot ▸ rfl`-style or build the per-`i`
equality as `congrArg₂ (·*·)`/`Mul.mul` from `hroot` and `rfl` for the
subtree part.  Steps 3–5 of the calc (bridge `sum_nbij'`,
`sum_coverSplit`, `sum_blockFunctional`) were never reached and remain
as designed; the 6-error count included their downstream noise.

## 6. Honesty invariant (unchanged)

All of this is M3 lattice-side.  None of it reduces M4/M5/Clay
(continuum limit, OS reconstruction, continuum gap — open mathematics).
Distance to Clay: **~0% (<0.1%)**.  Keep it written everywhere.
