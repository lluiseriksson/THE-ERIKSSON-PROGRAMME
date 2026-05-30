# Formalization plan — Kotecký–Preiss polymer cluster expansion in Lean

**Status: design only. Nothing here is implemented.** This is a concrete starting
blueprint for a (later, stronger) prover to build the polymer / cluster-expansion
layer that the Eriksson paper's §5 (terminal clustering) and §6.2 (single-scale UV
bound) rest on, and whose abstract endpoint is **Appendix A, Prop. A.1**
(`KP bound ⇒ exponential decay of truncated correlations`).

The code blocks below are **illustrative Lean signatures**, not compiled. They are
written so that proofs are `sorry`-free *targets*, never axioms. Per the project's
discipline (`FOUNDATIONS.md`), this file lives in `docs/` and is **not** part of the
verified `YangMillsCore`; it must never be imported into the core with `sorry`s.

> Honest difficulty: this is a **multi-month, novel formalization project**. To our
> knowledge there is **no polymer cluster expansion in Mathlib** as of 2026-05.
> Landing it would be a Mathlib-grade contribution useful far beyond this repo, and
> it is exactly milestone **M3** of `ROADMAP.md`: large, but *known mathematics*
> (not open). Do not expect to close it in a session.

---

## 0. Goal and what it unlocks

Formalize the abstract Kotecký–Preiss theorem and its corollary used by the paper:

> **(Appendix A, Prop. A.1)** For a hard-core polymer gas with activities `z(X)`
> satisfying a KP smallness criterion, the truncated two-point function decays
> exponentially: `|Cov(F,G)| ≤ C ‖F‖ ‖G‖ exp(−m · dist(supp F, supp G))`.

This `m > 0` is the terminal mass `m*` consumed as a **hypothesis** by
`YangMills/Paper/MassGapAssembly.lean` (`mass_gap_bound`, §7). Discharging Prop. A.1
turns that hypothesis from "assumed" to "derived from the KP bound" — i.e. it makes
the §5 input of the assembly genuine. (The §6.2 single-scale bound uses the same
machinery at each RG scale.)

It does **not** discharge where the KP bound itself comes from (Paper [1], extracted
from Balaban's activity estimates) — that remains the imported, hard input.

---

## 1. What Mathlib provides / lacks

**Has (reuse):** `Finset`, `Finset.sum`/`prod`, `Multiset`, `SimpleGraph` (for the
incompatibility graph and connectivity), `tsum`/`Summable` and absolute convergence,
`Real.exp` and monotonicity, geometric-series bounds (used already in
`UVSummation.lean`), `NNReal`/`ENNReal`.

**Lacks (must build):** polymer models, the polymer partition function, the
**Ursell/Mayer cluster coefficients**, the **cluster (Mayer) expansion of `log Ξ`**,
the **Kotecký–Preiss convergence criterion and its inductive proof**, and the
**truncated-correlation cluster representation**. None of this exists in Mathlib.

---

## 2. Recommended route

Use the **inductive Kotecký–Preiss proof** (Kotecký–Preiss, CMP 103 (1986)), in the
clean self-contained exposition of **Friedli–Velenik, _Statistical Mechanics of
Lattice Systems_, Ch. 5** (esp. Thm 5.4 and §5.7.1). Reasons:

* It avoids the Penrose/Brydges–Federbush **tree-graph inequality** (a separate hard
  combinatorial theorem) — KP's induction bounds the one-point cluster sum directly.
* The convergence is proved by induction on the number of polymers in a cluster,
  which maps well to Lean structural/strong induction.
* Friedli–Velenik state every constant and inequality explicitly (good for porting).

Alternative (if a tree-graph identity is later wanted for sharper constants):
Brydges–Kennedy / Bissacot–Fernández–Procacci — heavier, defer.

---

## 3. Layered Lean architecture (illustrative signatures)

### KP0 — Polymer substrate

```lean
/-- An abstract hard-core polymer system with complex activities. -/
structure PolymerSystem where
  Polymer    : Type*
  [decEq     : DecidableEq Polymer]
  incomp     : Polymer → Polymer → Prop          -- "incompatible" (overlap/touch)
  incomp_symm : ∀ X Y, incomp X Y → incomp Y X
  incomp_self : ∀ X, incomp X X                  -- hard core
  activity   : Polymer → ℂ                       -- z(X)

variable (P : PolymerSystem)

/-- A polymer family is *admissible* if its polymers are pairwise compatible. -/
def Admissible (S : Finset P.Polymer) : Prop :=
  ∀ X ∈ S, ∀ Y ∈ S, X ≠ Y → ¬ P.incomp X Y
```

### KP1 — Partition function (finite volume)

```lean
/-- Polymers "living in" a finite region `Λ : Finset Polymer`. -/
def partition (Λ : Finset P.Polymer) : ℂ :=
  ∑ S ∈ Λ.powerset.filter (Admissible P), ∏ X ∈ S, P.activity X
-- Ξ(Λ) = Σ over admissible subfamilies of the product of activities.
```

### KP2 — Cluster expansion and the KP criterion (the heart)

```lean
/-- The Kotecký–Preiss smallness criterion: there is a weight `a ≥ 0` with
    `∑_{Y incompatible with X} |z(Y)| · exp(a Y) ≤ a X`  for every polymer `X`. -/
def KPCriterion (a : P.Polymer → ℝ) : Prop :=
  (∀ X, 0 ≤ a X) ∧
  ∀ X, Summable (fun Y => if P.incomp X Y then ‖P.activity Y‖ * Real.exp (a Y) else 0) ∧
       (∑' Y, if P.incomp X Y then ‖P.activity Y‖ * Real.exp (a Y) else 0) ≤ a X

/-- Ursell/Mayer cluster coefficient of an (ordered) tuple of polymers, the sum over
    connected spanning subgraphs of the incompatibility graph of `(−1)^{edges}`. -/
noncomputable def ursell : List P.Polymer → ℚ := sorry   -- TARGET (combinatorial)

/-- **KP convergence (Friedli–Velenik Thm 5.4).** Under the KP criterion, the
    one-point cluster sum is bounded by `exp(a X) − 1`; hence the cluster expansion
    of `log Ξ` converges absolutely, uniformly in the volume. -/
theorem kp_cluster_convergence {a} (hKP : KPCriterion P a) (X : P.Polymer) :
    (∑' clusters containing X, |ursell …| * ∏ ‖activity‖) ≤ Real.exp (a X) - 1 := sorry
```

The induction (FV Thm 5.4): bound `Σ_{clusters ∋ X of n polymers}` by induction on
`n`, peeling one polymer and using the KP criterion to control the branching. This is
the single hardest lemma; budget most of the effort here.

### KP3 — Truncated correlation decay (= Appendix A, the payoff)

```lean
/-- Truncated two-point function as a sum over clusters connecting the supports. -/
-- def truncatedCorr (F G : Observable) : ℂ := ∑' clusters linking supp F, supp G, …

/-- **Appendix A, Prop. A.1.** KP convergence ⇒ exponential decay of covariances,
    with rate `m` from the KP weight and the per-polymer size penalty. -/
theorem kp_exponential_clustering
    {a} (hKP : KPCriterion P a) (hpen : SizePenalty P a m) (F G : …) :
    ‖truncatedCorr P F G‖ ≤ C * ‖F‖ * ‖G‖ * Real.exp (-(m * dist (supp F) (supp G))) := sorry
```

Any cluster linking `supp F` to `supp G` contains a connected chain spanning the
distance; the KP weights give an exponential penalty in that length. Summation over
such clusters uses `kp_cluster_convergence`. The output `m` is exactly the `mstar`
hypothesis of `mass_gap_bound`.

---

## 4. Milestones (with honest difficulty)

| ID | Content | Difficulty | Notes |
|----|---------|-----------|-------|
| **KP0** | `PolymerSystem`, `Admissible`, `partition` | low | ✅ **landed** — `YangMills/KP/Basic.lean` (`PolymerSystem`, `Admissible` + `admissible_empty`/`_mono`/`_singleton`, `partition`, `partition_empty = 1`); green, oracle clean. |
| **KP1** | finite-volume `Ξ`, basic identities (factorization over compatible blocks) | low–med | ✅ **landed** — `YangMills/KP/Basic.lean`: `partition_singleton` (`Ξ({X})=1+z(X)`), `admissible_union_iff`, and the factorization `partition_union` (`Ξ(Λ₁∪Λ₂)=Ξ(Λ₁)·Ξ(Λ₂)` for disjoint, cross-compatible blocks); green, oracle clean. This is the multiplicativity that makes `log Ξ` additive. |
| **KP2a** | `ursell` coefficients + connected-cluster indexing | **high** | ✅ **defined** — `YangMills/KP/Cluster.lean` (`incompGraph`, `incompGraph_adj`, `IsCluster`) + `YangMills/KP/Ursell.lean` (`ursell` = signed sum `∑(−1)^{#edges}` over connected spanning subgraphs of the incompatibility graph, plus `ursell_fin_one` (`φ = 1` for a single-polymer cluster — base case) `ursell_eq_zero_of_not_isCluster` (`φ = 0` off clusters — clusters are *exactly* the expansion index), and `ursell_fin_two` (`φ = −1` for a dimer — the first nontrivial Mayer coefficient, validating the definition against the physical values +1/−1/0)); green, oracle clean. **Next:** the expansion identity `log Ξ = ∑ clusters …`, then KP2b convergence. |
| **KP2b** | `kp_cluster_convergence` (FV Thm 5.4, inductive) | **highest** | 🚧 **attack begun** — `YangMills/KP/Expansion.lean`: `clusterSum` (the RHS object `∑' n, (1/(n+1)!)·∑_X φ(X)·∏z`, for `Fintype Polymer`) is defined and oracle-clean. The crux (convergence + the identity) is below. |

### KP2b attack plan (the expansion identity `Ξ = exp(clusterSum)`)

The cluster sum (RHS) is now a Lean object (`clusterSum`). The route to the identity
`log Ξ(Λ) = clusterSum` and the convergence, in dependency order:

- **E1 — cluster sum object.** ✅ `clusterSum` defined (`Expansion.lean`).
- **E2 — only-clusters reduction.** ✅ `ursell_eq_zero_of_not_isCluster` already
  shows the inner sum ranges effectively over clusters.
- **E3 — Mayer exponential formula (combinatorial identity).** `Ξ(Λ) = exp(clusterSum)`
  as a *formal* identity of finite sums (no convergence yet): expand `exp` of the
  cluster sum into a sum over multisets of clusters, and match it term-by-term with
  `Ξ = ∑_{compatible families} ∏ z` via the Mayer–Ursell inversion. This is the
  combinatorial heart; needs the partition of a polymer family into its connected
  components (`incompGraph` connected components) and the multinomial/`n!`
  bookkeeping. Large but finitary.
- **E4 — KP convergence (FV Thm 5.4).** The inductive bound: under `KPCriterion`,
  the one-point cluster sum is `≤ exp(a X) − 1`, so `clusterSum` converges
  absolutely uniformly in the volume. Strong induction on cluster size. **The crux.**
- **E5 — truncated correlation decay (= Appendix A / KP3).** Differentiate `log Ξ`
  / use the cluster representation of the two-point function; the KP weights give
  the exponential-in-distance bound `m*` fed to `mass_gap_bound` (§7).

E3 is the next attackable target (finitary, no convergence); E4 is the months-long
inductive core.

### Landed so far (`YangMills/KP/`, all oracle-clean, wired into `YangMillsCore`)

KP0–KP2a: `PolymerSystem`, `partition`, `partition_empty/_singleton/_union`,
`incompGraph`, `IsCluster`, `ursell`, `ursell_fin_one` (φ=+1), `ursell_fin_two`
(φ=−1), `ursell_eq_zero_of_not_isCluster`.

KP2b identity side (`Expansion.lean`): `clusterSum` (E1), `clusterSum_eq_sum_clusters`
(E2), `expansion_identity_isEmpty` (E3 base), `clusterSum_first_order` (E3 linear order).

KP2b convergence side (`Criterion.lean`): `KPCriterion`, `kp_activity_le`,
`kp_neighbor_sum_le`.

### The two heavy open targets (sharpened goals for the next prover)

Both are genuine theorems *not* in Mathlib; each is a dedicated-session effort, not an
iteration. They have no remaining 3-line intermediate corollaries — the next step in
each *is* the heavy theorem.

> **Progress (dedicated session, Target A).** The `decide` tactic settles connectivity
> of concrete `fromEdgeSet` subgraphs on `Fin n` *kernel-side* (oracle stays clean), so
> small complete-graph cases are computable. Landed: `ursell_fin_three` (φ(K₃)=+2, the
> k=2 checkpoint), confirming the pattern at +1,−1,+2. Piece 1 of the recurrence
> (`∑_{E⊆AllEdges}(−1)^{|E|} = [AllEdges=∅]`) is already in Mathlib as
> `Finset.sum_powerset_neg_one_pow_card`. The back-half induction
> `closed_form_of_recurrence` (recurrence ⟹ `(−1)^k k!`) is proved. **Target A is now
> reduced to a single open lemma:** the recurrence `ursell(K_{k+1}) = −k · ursell(K_k)`,
> i.e. the component-of-vertex-0 decomposition of spanning subgraphs (the only piece
> needing Mathlib's connected-component API). No axiom introduced — the recurrence is
> carried as the explicit hypothesis `hrec` of `closed_form_of_recurrence`.

**Target A — Ursell value on the complete graph (closes E3 beyond linear order).**
The Mayer coefficient of a `k`-fold cluster of a single polymer (whose incompatibility
graph is `K_k`, since the hard core makes every pair incompatible) is

```
theorem ursell_complete {k : ℕ} (X : Fin (k+1) → P.Polymer)
    (hcomplete : ∀ i j, i ≠ j → P.incomp (X i) (X j)) :
    ursell P X = (-1) ^ k * (Nat.factorial k : ℤ)
```

i.e. `φ(K_{k+1}) = (−1)^k k!`. Validated data: `k=0 → +1` (`ursell_fin_one`),
`k=1 → −1` (`ursell_fin_two`); next checkpoint `k=2 → +2`. Proof route: the signed
count of connected spanning subgraphs of `K_{k+1}`; either deletion–contraction
induction or the exponential-generating-function identity `log(1+z) = ∑ (−1)^k z^{k+1}/(k+1)`.
The Lean obstacle is walk-based reachability arguments on `fromEdgeSet` subgraphs
(showing specific subsets are/aren't connected), for which Mathlib has only low-level
API. With Target A, `clusterSum` of a one-polymer system sums to `log(1 + z(X))`,
giving the single-polymer case of `Ξ = exp(clusterSum)`.

#### Blueprint for the one remaining lemma — the recurrence `d(n+1) = −n·d(n)`

Verified scaffolding already in `Ursell.lean`: `ursellComplete` (= `d(n)`),
`closed_form_of_recurrence` (recurrence ⟹ closed form), `ursellComplete_one/two/three`
(`d=1,−1,2`), and `allSubgraphs_signedSum` (`a(n) = ∑_{E⊆E(K_n)}(−1)^{|E|} = [n≤1]`).
The recurrence follows from the **component-of-vertex-0 decomposition**:

1. Component map `c0 : E(K_n).powerset → {S : Finset (Fin n) // 0 ∈ S}`,
   `E ↦ ((fromEdgeSet ↑E).connectedComponentMk 0).supp`. (Mathlib:
   `SimpleGraph.ConnectedComponent.supp`, `connectedComponentMk_mem`.)
2. `Finset.sum_fiberwise` over `c0`: `a(n) = ∑_{S∋0} ∑_{E : c0 E = S} (−1)^{|E|}`.
3. Fiber bijection (the crux): `{E : c0 E = S} ≃ {connected spanning subgraphs of K_S}
   × {arbitrary subgraphs of K_{Sᶜ}}`. Forward: split `E` into `E∩K_S` and `E∩K_{Sᶜ}`;
   the no-crossing-edges fact (`connectedComponentMk_eq_of_adj`: adjacent vertices share
   a component, so no edge leaves `S`) makes this a partition of `E`. So the fiber sum
   factors as `d(|S|)·a(n−|S|)`.
4. Group by `|S| = k` (`C(n−1,k−1)` choices of `S∋0`): `a(n) = ∑_k C(n−1,k−1) d(k) a(n−k)`.
5. With `a(n) = [n≤1]` (step done) only `k = n` and `k = n−1` survive for `n ≥ 2`,
   giving `0 = d(n) + (n−1)d(n−1)`, i.e. `d(n) = −(n−1)d(n−1)`. Reindex to `hrec`.

Step 3 is the substantial piece (needs a `Finset`-level subgraph-splitting bijection and
the component API); it is a focused local-Lean effort, not a paste-loop iteration.

##### Exact next target (for an interactive-Lean session)

All structural sub-lemmas are now landed and oracle-clean in `Ursell.lean`:
`componentSupp_closed_under_adj` (no edge leaves a component — the partition fact),
plus `allSubgraphs_signedSum` (`a(n)=[n≤1]`), `ursellComplete{,_one,_two,_three}`,
`closed_form_of_recurrence`, `ursellComplete_closed_form`. Mathlib supplies the rest of
the component API: `ConnectedComponent.supp`, `mem_supp_congr_adj`,
`connected_toSimpleGraph` (induced subgraph on a component is connected),
`maximal_connected_induce_supp`, and `Finset.sum_fiberwise` / `Finset.sum_nbij'`.

The single remaining lemma to prove interactively (after which `ursellComplete_closed_form`
becomes unconditional):

```lean
theorem ursellComplete_recurrence (n : ℕ) (hn : 1 ≤ n) :
    ursellComplete (n + 1) = -(n : ℤ) * ursellComplete n
```

Proof skeleton:
1. `unfold ursellComplete ursell`; the LHS is `∑_{E ⊆ E(K_{n+1})} [connected] (−1)^{|E|}`.
   Drop the `[connected]` filter is *not* valid here — instead keep the full powerset and
   use `componentSupp_closed_under_adj` to fiber.
2. Fiber the full signed sum `a(n+1) = ∑_{E ⊆ E(K_{n+1})} (−1)^{|E|}` by
   `S := (fromEdgeSet ↑E).connectedComponentMk 0 |>.supp.toFinset` (the component of 0).
   `Finset.sum_fiberwise`.
3. For fixed `S ∋ 0`: the fiber `{E : comp₀ = S}` splits (via
   `componentSupp_closed_under_adj`, no crossing edges) as `{connected spanning E_S of K_S}
   × {arbitrary E_c ⊆ E(K_{Sᶜ})}`, with `|E| = |E_S| + |E_c|`. Hence the fiber sum is
   `(∑_{E_S connected} (−1)^{|E_S|}) · (∑_{E_c} (−1)^{|E_c|}) = ursellComplete |S| · a(n+1−|S|)`.
4. By `allSubgraphs_signedSum`, `a(m) = [m≤1]`, so on the LHS `a(n+1) = 0` (as `n+1 ≥ 2`),
   and on the RHS the complement factor `a(n+1−|S|)` is `0` unless `|S| ∈ {n, n+1}`.
5. `|S| = n+1` ⟹ term `= ursellComplete(n+1)·a(0) = ursellComplete(n+1)`.
   `|S| = n`   ⟹ `n` choices of which vertex ≠ 0 is excluded? No — `S ∋ 0` and `|S|=n`
   means one non-zero vertex is excluded: `n` such `S`, each giving
   `ursellComplete(n)·a(1) = ursellComplete(n)`. So `0 = ursellComplete(n+1) + n·ursellComplete(n)`,
   i.e. the recurrence. (Use `componentSupp_closed_under_adj` to show a `|S|=n` component
   forces the excluded vertex isolated, consistent with `comp₀ = S`.)

The hard Lean work is the step-3 fiber bijection as a `Finset.sum_nbij'` between
`(E(K_{n+1})).powerset.filter (comp₀ = S)` and a product of two powerset-filters; the
`|E| = |E_S| + |E_c|` cardinality split; and the `decide`-free connectivity reasoning on
`fromEdgeSet` of the `S`-part. Budget this as one dedicated interactive session.

**Target B — inductive KP convergence (closes E4 / FV Thm 5.4).**
Under `KPCriterion P a`, the cluster sum converges absolutely with the standard bound

```
theorem kp_cluster_bound [Fintype P.Polymer] {a : P.Polymer → ℝ}
    (h : KPCriterion P a) (X : P.Polymer) :
    ∑ (clusters containing X) ‖φ(·)‖ ∏ ‖z‖ ≤ a X          -- schematic
```

(the one-point cluster sum is `≤ a X`), proved by strong induction on cluster size via
the tree-graph inequality. `kp_activity_le` and `kp_neighbor_sum_le` are the base
estimates the induction starts from. The Lean obstacle is the tree-graph / Penrose
bound combinatorics (forests spanning the incompatibility graph), entirely absent from
Mathlib. Target B feeds the exponential-clustering corollary (KP3) and ultimately the
`m*` fed to `mass_gap_bound` (§7).
| **KP3** | `kp_exponential_clustering` (Appendix A) | med–high | Given KP2b, this is "spanning cluster pays e^{−m·dist}" + summation. |
| **KP4** | wire `m*` into `mass_gap_bound` (§7); state §5 as a theorem, not a hypothesis | low | The payoff: §5 input becomes derived from the KP bound. |

Estimated total: **multi-month**, KP2b dominating. Each milestone should land green
with oracle `[propext, Classical.choice, Quot.sound]` and no `sorry` before the next
begins (the project rule).

---

## 5. Where it leaves the honest picture

Completing KP0–KP4 would discharge the §5 (and, with the per-scale version, §6.2)
inputs of the already-formalized `mass_gap_bound` — turning the conditional lattice
mass-gap **assembly** into one resting only on the **KP bound of Paper [1]** (still
imported) and Balaban's framework. It would be a major, genuinely valuable
formalization milestone (M3).

It would **not** reach the Clay theorem: OS1 / full O(4) covariance and the continuum
construction (M4/M5, `ROADMAP.md`) remain open mathematics, and the KP input itself
(Paper [1], from Balaban's estimates) remains unformalized/imported. The honest
percentage ledger of `ROADMAP.md §0` is unchanged by *planning* this; it moves only
when the lemmas land green and survive an adversarial audit.
