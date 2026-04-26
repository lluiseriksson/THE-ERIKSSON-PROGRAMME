# MATHLIB_GAPS.md

**Author**: Cowork agent (Claude), inventory pass 2026-04-25
**Subject**: concrete Mathlib lemmas / definitions needed for F3 closure,
sized and ordered for upstream contribution
**Companion documents**: `BLUEPRINT_F3Count.md`, `BLUEPRINT_F3Mayer.md`,
`PETER_WEYL_AUDIT.md`, **`MATHLIB_PRS_OVERVIEW.md`** (the *opposite* direction — what we contribute to Mathlib)

> **Cross-reference (Phase 422, 2026-04-25)**: of the 5 gaps below, **gap 1 is now drafted in `mathlib_pr_drafts/KlarnerBFSBound_PR.lean`** and **gap 4's foundational ingredient (Brydges-Kennedy `|exp(t)-1| ≤ |t|·exp(|t|)`) is drafted in `mathlib_pr_drafts/BrydgesKennedyBound_PR.lean`**. Status: workspace-produced drafts only, NOT built with `lake build`. See `MATHLIB_PRS_OVERVIEW.md` §6 for details. Gaps 2, 3, 5 remain as stated below.

---

## 0. TL;DR

Five concrete gaps. None individually blocks F3 closure (all admit
in-repo workarounds), but **all five are reusable beyond this project**
and have positive expected value as Mathlib PRs. Ordered by ratio
(value to formalised math community) / (effort):

1. **BFS-tree lattice animal count bound** — *small PR, high value*.
   Provides `(2d−1)^(m−1)` upper bound on connected animals of size
   `m` in `ℤ^d` containing a fixed point. ~150 LOC. **Recommend yes**.
   **STATUS (Phase 422)**: drafted as `mathlib_pr_drafts/KlarnerBFSBound_PR.lean`,
   pending `lake build` polish.
2. **Haar product factorisation on disjoint link sets** — *small PR,
   medium value*. Specialises `MeasureTheory.Measure.pi` to the case
   where two product factors share no coordinates. ~100 LOC.
   **Recommend yes**. *(Older draft `PiDisjointFactorisation.lean` exists; not in current 17-file PR-ready set.)*
3. **Möbius / Ursell truncation identity for finite partition
   lattices** — *medium PR, medium value*. The combinatorial inversion
   that turns full cluster averages into truncated activities. ~400
   LOC. **Recommend defer** — workable in-repo via the BK
   reformulation that bypasses it. *(Older draft `PartitionLatticeMobius.lean` exists; not in current 17-file PR-ready set.)*
4. **Brydges–Kennedy / Battle–Federbush forest estimate** — *large PR,
   high value*. The cluster-expansion analytic core. ~800-1500 LOC,
   significant analysis content. **Recommend in-repo** for the
   project's timeline; revisit upstream after Clay closure.
   **STATUS (Phase 422)**: foundational per-edge ingredient
   `|exp(t) - 1| ≤ |t| · exp(|t|)` drafted as
   `mathlib_pr_drafts/BrydgesKennedyBound_PR.lean`. The full forest
   estimate remains in-repo work.
5. **Spanning-tree count via Cayley's formula** — *medium PR, low
   incremental value*. Mathlib has `SimpleGraph.spanningTree` but not
   the explicit count `n^(n−2)`. ~300 LOC. **Recommend skip** — the
   F3 path bypasses this entirely (BK works with the bound, not the
   exact count).

The first two are no-regret PRs Lluis can hand off when the team has
spare cycles. The other three should remain in-repo until after the
project's Clay closure target lands.

> **Note (2026-04-25)**: The 17-file PR-ready collection in
> `mathlib_pr_drafts/` contains **12 elementary `Real.exp` /
> `Real.log` / hyperbolic / numerical / matrix lemmas NOT listed
> above** — they were factored out of the project's downstream
> consumers, not from F3 specifically. See `MATHLIB_PRS_OVERVIEW.md`
> for the outward catalog. This `MATHLIB_GAPS.md` document remains
> scoped to **F3-closure-specific** Mathlib needs.

---

## 1. Method

For each gap I record:
- **Statement**: the Mathlib-grade theorem desired.
- **Why it's needed**: which F3 step consumes it.
- **Current Mathlib status**: AVAILABLE / PARTIAL / MISSING with
  pointers.
- **Effort estimate**: rough LOC + complexity tier.
- **In-repo workaround**: what the project does if upstream lands
  late or never.
- **Recommendation**: PR or in-repo.

---

## 2. Gap 1 — BFS-tree lattice animal count bound

### Statement (target Mathlib form)

```lean
theorem Finset.card_connectedSubsets_anchored_le_pow
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_deg : ∀ v : V, G.degree v ≤ Δ)
    (root : V) (m : ℕ) :
    ((Finset.univ : Finset (Finset V)).filter
      (fun S => root ∈ S ∧ S.card = m ∧
        (G.induce S).Connected)).card ≤
      (Δ - 1) ^ (m - 1) * Δ
```

(Specialisation: for `ℤ^d` plaquette adjacency graph with `Δ = 2d`,
this gives the connective-constant bound.)

### Why it's needed

This is the core combinatorial input for `BLUEPRINT_F3Count.md`
Resolution C, witnessing
`ShiftedConnectingClusterCountBoundExp 1 (2d-1)`. The proof
classically goes via BFS enumeration:
- Start at `root`, build `S` one vertex at a time.
- At each step, the new vertex must be adjacent to the current frontier.
- The current frontier has at most `(Δ - 1) * (current size)` candidates,
  but only `Δ - 1` "fresh" choices per active boundary vertex.
- A more careful bookkeeping (Klarner–Rivest) gives the
  `(Δ - 1)^(m-1) * Δ` bound.

### Current Mathlib status

**MISSING**. Mathlib has `SimpleGraph.Connected`, `SimpleGraph.induce`,
but no upper-bound theorem on the number of connected subgraphs of
fixed cardinality. The closest existing material is
`SimpleGraph.spanningTree` (existence) and `SimpleGraph.adjMatrix`
(spectral), neither of which gives the count.

### Effort estimate

~150 LOC. Low complexity (induction on `m`, careful bookkeeping). No
new definitions beyond the statement.

### In-repo workaround

Direct Lean proof in `YangMills/ClayCore/LatticeAnimalCount.lean`,
specialised to `ConcretePlaquette d L` (lattice plaquette graph)
rather than abstract `SimpleGraph`. Saves the abstraction overhead
but loses Mathlib reusability. Same ~150 LOC.

### Recommendation

**PR upstream** as `Mathlib.Combinatorics.SimpleGraph.AnimalCount` or
similar. High value beyond this project (anyone formalising
percolation, statistical mechanics, or lattice theory benefits). Low
risk PR — the proof is bounded and self-contained.

---

## 3. Gap 2 — Haar product factorisation on disjoint link sets

### Statement (target Mathlib form)

```lean
theorem MeasureTheory.Measure.pi_integral_factorise_disjoint
    {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)]
    {S T : Finset ι} (h_disj : Disjoint S T)
    (f : (∀ i ∈ S, α i) → ℝ)
    (g : (∀ i ∈ T, α i) → ℝ)
    (hf : Integrable f (Measure.pi (fun i : S => μ i)))
    (hg : Integrable g (Measure.pi (fun i : T => μ i))) :
    ∫ x, (f (x ∘ ...)) * (g (x ∘ ...)) ∂(Measure.pi μ) =
    (∫ y, f y ∂(Measure.pi (fun i : S => μ i))) *
    (∫ z, g z ∂(Measure.pi (fun i : T => μ i)))
```

(There are several equivalent forms; the ergonomically useful one in
`HaarFactorization.lean` extracts disjoint link sets from the gauge
configuration product space.)

### Why it's needed

This is the **Fubini lemma** that lets the BK truncated activity
vanish for non-`PolymerConnected` polymers (`BLUEPRINT_F3Mayer.md`
§3.5): if `Y = Y₁ ⊔ Y₂` decomposes into edge-disjoint pieces, then
the BK integrand factorises and the zero-mean of `w̃` on `Y₂`
contributes 0 to the truncated activity.

### Current Mathlib status

**PARTIAL**. Mathlib has:
- `MeasureTheory.Measure.pi`, `MeasureTheory.integral_pi`,
  `MeasureTheory.integral_prod`.
- `MeasureTheory.Integrable.integral_pi` for general products.

What is missing is the specific re-arrangement for disjoint subsets
of a finite index type, expressed in a form ergonomically useful for
gauge-link products. The repo's `FubiniCluster.lean` has a
project-local version specialised to plaquette polymers, ~150 LOC.

### Effort estimate

~100 LOC for a Mathlib-grade general statement. Low complexity (it's
an unfolding of `Measure.pi` followed by `Fubini`).

### In-repo workaround

`FubiniCluster.lean` already exists; it covers the project's needs.
The Mathlib upstream version would be a generalisation, not a
prerequisite.

### Recommendation

**PR upstream** as a small addition to
`Mathlib.MeasureTheory.Constructions.Pi`. Useful for any project that
deals with product measures and disjoint coordinate factorisation
(probability theory, statistical physics, formal verification of
distributed systems). Medium value, very low risk.

---

## 4. Gap 3 — Möbius / Ursell truncation identity

### Statement (target Mathlib form)

```lean
theorem Combinatorics.partitionLattice_mobius_inversion
    {α : Type*} [DecidableEq α] (S : Finset α)
    (f g : Finset α → ℝ)
    (h : ∀ T ⊆ S, f T = ∑ π ∈ Finpartition.univ T, ∏ B ∈ π.parts, g B) :
    ∀ T ⊆ S, g T = ∑ π ∈ Finpartition.univ T,
      (-1) ^ (π.parts.card - 1) * (π.parts.card - 1).factorial *
      ∏ B ∈ π.parts, f B
```

(The classical Möbius inversion on the partition lattice, Stanley
*Enumerative Combinatorics* vol. 1, Ch. 3.)

### Why it's needed

The truncated cluster activity `K(Y)` is defined as the Möbius
inverse of the ordinary cluster average over partitions of `Y`.
Without this lemma, the BK construction has to define `K(Y)` directly
via the interpolation formula and then prove independently that it
agrees with the Möbius inverse — workable but more roundabout.

### Current Mathlib status

**MISSING**. Mathlib has `Finpartition`, `Order.Mobius` for general
posets, and `Combinatorics.Partition` for integer partitions, but the
partition-lattice Möbius function is not formalised, and the
inversion theorem specialised to it is not present.

### Effort estimate

~400 LOC. Medium complexity. Requires building the partition
lattice as a `Lattice` instance (or specialised structure), proving
the Möbius function is `(-1)^(k-1) * (k-1)!` (Stanley Prop 3.10.4 or
similar), and the inversion theorem.

### In-repo workaround

Skip Möbius entirely. The BK construction in
`BLUEPRINT_F3Mayer.md` §3.1 defines `K(Y)` via the interpolation
formula directly, no Möbius needed. The truncation property
(`K({r}) = 0` etc.) follows from the interpolation formula + zero-
mean of `w̃`, not from Möbius.

### Recommendation

**Defer**. The in-repo workaround is clean and the Mathlib PR has a
significant surface area for a feature that is only marginally
useful in the F3 chain. Revisit after Clay closure if there is
appetite for a "Möbius / partition lattice" Mathlib PR independently.

---

## 5. Gap 4 — Brydges–Kennedy / Battle–Federbush forest estimate

### Statement (target Mathlib form, simplified)

```lean
/-- Brydges-Kennedy forest estimate.

Given a polymer Y, a probability measure μ on the gauge group, and a
zero-mean fluctuation `w̃ : G → ℝ` with sup-norm `M = ||w̃||_∞`, the
Brydges-Kennedy interpolation truncation `K(Y)` of the ordinary cluster
average satisfies `|K(Y)| ≤ M^|Y|`. -/
theorem ClusterExpansion.brydgesKennedy_estimate
    {G : Type*} [TopologicalGroup G] [CompactSpace G]
    (μ : ProbabilityMeasure G) (w̃ : C(G, ℝ))
    (h_zero_mean : ∫ g, w̃ g ∂μ = 0)
    (Y : Finset (...))
    (K : ℝ := truncatedCluster μ w̃ Y) :
    |K| ≤ (‖w̃‖∞) ^ Y.card
```

### Why it's needed

This is **the** analytic core of `BLUEPRINT_F3Mayer.md` §3.2. Without
it, the bound `|K(Y)| ≤ A₀ · r^|Y|` collapses to a super-exponential
estimate (factorial blowup) and the cluster expansion does not
converge.

### Current Mathlib status

**MISSING entirely**. Cluster expansion is a substantial chapter of
classical statistical mechanics that has not been formalised in Lean
4 (or Mathlib in any other form). Some related infrastructure:
- `MeasureTheory.IntegralAverage` (basic).
- `MeasureTheory.IntegrableOn.continuousOn_compact`.

### Effort estimate

~800–1500 LOC. High complexity. Requires:
- The interpolation polynomial in `s_1, ..., s_|Y|−1`.
- The forest enumeration.
- The Cayley-formula tree count.
- The integral bound and the recursion that yields the
  factorial-cancellation.

This is **roughly half of a small mathematics paper formalised**.

### In-repo workaround

Implement directly in `YangMills/ClayCore/BrydgesKennedyEstimate.lean`,
specialised to the Wilson plaquette setting. Saves the abstraction tax
(no need to factor through `TopologicalGroup`, `ProbabilityMeasure`,
`C(G,ℝ)` infrastructure that may not exist in the right shape).
Same ~800–1500 LOC.

### Recommendation

**In-repo for now, upstream after Clay closure**. The Mathlib PR is
too heavy to land on the project's critical path, but the proof is
genuinely valuable as a community contribution and should be revisited
once the project's main target is achieved. Coordinate with
Mathlib maintainers (Yury Kudryashov, Floris van Doorn) as a likely
candidate when the time comes.

---

## 6. Gap 5 — Spanning-tree count via Cayley's formula

### Statement (target Mathlib form)

```lean
theorem SimpleGraph.completeGraph_spanningTreeCount
    (n : ℕ) (h : 2 ≤ n) :
    (SimpleGraph.completeGraph (Fin n)).spanningTrees.card = n ^ (n - 2)
```

### Why it's needed

The BK estimate naively uses Cayley's formula to count trees on `Y`.
However, the **upper bound** `treeCount ≤ n^(n-2)` is sufficient (and
indeed weaker bounds work too); the **exact count** is overkill.

### Current Mathlib status

**MISSING**. Mathlib has `SimpleGraph.spanningTree` (existence as a
subgraph) and `IsSpanningSubgraph`, but no count theorem and no
`spanningTrees : Finset` enumerator.

### Effort estimate

~300 LOC. Medium complexity. Cayley's formula has several proofs
(Prüfer sequences, double counting, deletion-contraction). The
Prüfer-sequence proof is most amenable to Lean.

### In-repo workaround

Bypass entirely. The BK estimate can be reformulated to use a weaker
bound (e.g., the trivial bound that `treeCount ≤ n^n` from picking
the parent of each non-root vertex independently — losing a factor of
`n^2` which is absorbed into constants). This loosens the convergence
constants in `BLUEPRINT_F3Mayer.md` §3.4 by a factor of `N_c^2` per
plaquette but does not change validity.

### Recommendation

**Skip**. The expected value of the upstream PR is low because the F3
path doesn't need the exact count, and the path forward in §6 of
BLUEPRINT_F3Mayer (Path A — using a weaker tree count) is cleaner.
Revisit if there is independent Mathlib appetite for Cayley's formula
(it is a famous theorem and would be a charming PR for whoever wants
the credit).

---

## 7. Summary table

| # | Gap | LOC | Risk | Value | Decision |
|---|-----|-----|------|-------|----------|
| 1 | BFS-tree animal count | ~150 | low | high | **PR upstream** |
| 2 | Haar disjoint factorisation | ~100 | low | medium | **PR upstream** |
| 3 | Möbius / partition lattice | ~400 | medium | medium | defer (workable in-repo) |
| 4 | Brydges–Kennedy forest estimate | ~1000 | high | high | **in-repo, upstream after Clay** |
| 5 | Cayley's formula | ~300 | medium | low | skip (bypass via weaker bound) |

**Total formalisation cost** if all five upstream:
~1950 LOC of Mathlib PRs.

**Total in-repo cost** if none upstream:
~1500 LOC (saves abstraction overhead).

**Recommended hybrid** (#1 and #2 upstream, #3-#5 in-repo):
~250 LOC upstream + ~1450 LOC in-repo = 1700 LOC total. Net cost ~250
LOC over pure in-repo, in exchange for two reusable Mathlib
contributions.

---

## 8. Action items

For Lluis (human review):

- [ ] Approve hybrid recommendation (PRs for #1 and #2, in-repo for
      the rest), or specify alternative.
- [ ] If yes, decide whether to draft the PRs yourself, delegate to
      Codex with explicit instructions, or invite a Mathlib
      contributor.

For Codex (autonomous):

- [ ] If hybrid approved: focus 24/7 cadence on the in-repo content
      (#4 BK estimate is the largest single block), and treat the
      upstream PRs as background work.
- [ ] If standalone: pursue the in-repo path for all five gaps.

For Cowork agent (next turn, if requested):

- [ ] Draft a literal PR text for Gap #1 (BFS-tree animal count) —
      the smallest, most actionable upstream contribution. Could
      serve as a template for the others.

---

*End of inventory. Last updated 2026-04-25.*
