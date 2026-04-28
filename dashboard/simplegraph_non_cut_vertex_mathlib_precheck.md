# Mathlib Pre-check: `SimpleGraphHighCardTwoNonCutExists`

**Cowork-authored Mathlib has-vs-lacks pre-check for the v2.61 pure finite-graph open def.**

**Author**: Cowork
**Created**: 2026-04-26T22:55:00Z (under `COWORK-MATHLIB-SIMPLEGRAPH-NON-CUT-VERTEX-PRECHECK-001`)
**Status**: **forward-looking blueprint only**. `SimpleGraphHighCardTwoNonCutExists` is **OPEN**; this document does not prove it. F3-COUNT remains `CONDITIONAL_BRIDGE`.

---

## Mandatory disclaimer

> The pure finite-graph statement `SimpleGraphHighCardTwoNonCutExists`
> ("every finite connected `SimpleGraph` with at least 4 vertices has 2
> non-cut vertices") is **OPEN**. This pre-check identifies the cheapest
> closure path among (1) existing Mathlib lemma, (2) short Mathlib PR, (3)
> in-project proof using existing Mathlib infrastructure. **Nothing in this
> document moves the F3-COUNT row from `CONDITIONAL_BRIDGE` or moves any
> percentage. All 4 percentages preserved at 5% / 28% / 23-25% / 50%.**

---

## The target

From `LatticeAnimalCount.lean:1888-1895` (v2.61.0):

```lean
def SimpleGraphHighCardTwoNonCutExists : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α),
    G.Connected →
    4 ≤ Fintype.card α →
    ∃ z₁, ∃ z₂,
      z₁ ≠ z₂ ∧
        (G.induce ({z₁}ᶜ : Set α)).Preconnected ∧
        (G.induce ({z₂}ᶜ : Set α)).Preconnected
```

In English: every finite connected graph with ≥ 4 vertices has at least 2 distinct vertices whose individual deletion preserves preconnectedness.

---

## Mathlib has-vs-lacks table

| # | Mathlib lemma | File:line | Has? | Role in closure |
|---:|---|---|:---:|---|
| 1 | `SimpleGraph.Connected` | `SimpleGraph/Connectivity/Connected.lean` | **HAS** | The basic predicate; first hypothesis of the open def |
| 2 | `SimpleGraph.Preconnected` | `SimpleGraph/Connectivity/Connected.lean` | **HAS** | The conclusion's predicate |
| 3 | `SimpleGraph.induce` | `SimpleGraph/Maps.lean` | **HAS** | Vertex-restricted induced subgraph (used in conclusion) |
| 4 | `SimpleGraph.IsTree` | `SimpleGraph/Acyclic.lean:51` | **HAS** | Connected + acyclic; the spanning-tree witness |
| 5 | `SimpleGraph.Connected.exists_isTree_le_of_le_of_isAcyclic` (and `.exists_isTree_le`) | `SimpleGraph/Acyclic.lean:472` | **HAS** | **Spanning tree exists for any finite connected G** — the engine |
| 6 | `SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial` | `SimpleGraph/Acyclic.lean:522-526` | **HAS** | Every nontrivial finite tree has ≥ 1 leaf |
| 7 | `SimpleGraph.IsTree.minDegree_eq_one_of_nontrivial` | `SimpleGraph/Acyclic.lean:507-519` | **HAS** | Stronger: minDegree of nontrivial finite tree is exactly 1 |
| 8 | `SimpleGraph.Connected.induce_compl_singleton_of_degree_eq_one` | `SimpleGraph/Acyclic.lean:530-540` | **HAS** | **Deleting a degree-1 vertex preserves connectedness** — the deletion engine |
| 9 | `SimpleGraph.Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial` | `SimpleGraph/Acyclic.lean:559-568` | **HAS** | **SINGLE-non-cut version of our target** (1 of 2 vertices needed) |
| 10 | `SimpleGraph.Connected.exists_preconnected_induce_compl_singleton_of_finite` | `SimpleGraph/Acyclic.lean:570-575` | **HAS** | Same as #9 but Preconnected (drops nontriviality requirement) |
| 11 | `SimpleGraph.Walk.IsPath` | `SimpleGraph/Walk/Basic.lean` | **HAS** | Path predicate (alternative proof route via longest path) |
| 12 | `SimpleGraph.IsAcyclic.path_unique` | `SimpleGraph/Acyclic.lean:191` | **HAS** | Trees have unique paths (alternative proof route) |
| 13 | `SimpleGraph.Subgraph.Connected` | `SimpleGraph/Connectivity/Subgraph.lean` | **HAS** | Subgraph-level connectivity |
| 14 | `Fintype.card`, `Finset.card_filter`, `Finset.sum_const` | `Mathlib/Data/Fintype/Card.lean` | **HAS** | Cardinality machinery for the counting argument |
| 15 | `SimpleGraph.sum_degrees_eq_twice_card_edges` | `SimpleGraph/DegreeSum.lean` | **HAS** | Handshaking lemma — needed for the "2 leaves" counting |
| **MISSING** | "**Every nontrivial finite tree has ≥ 2 leaves**" | not in Mathlib (as of search) | **LACKS** | The single missing piece |
| **MISSING** | "**Every finite connected SimpleGraph with ≥ 4 vertices has 2 non-cut vertices**" (= our exact target) | not in Mathlib | **LACKS** | The composed target itself |

---

## Decisive observation: Mathlib already has the SINGLE-non-cut version

**`SimpleGraph.Connected.exists_preconnected_induce_compl_singleton_of_finite`** (Acyclic.lean:570-575):

```lean
lemma Connected.exists_preconnected_induce_compl_singleton_of_finite [Finite V]
    (hconn : G.Connected) : ∃ v : V, (G.induce {v}ᶜ).Preconnected
```

This is **exactly half of our target** — the existence of ONE non-cut vertex. The proof recipe (Acyclic.lean:561-568) is:

```lean
obtain ⟨T, _, T_isTree⟩ := hconn.exists_isTree_le      -- spanning tree
have ⟨hT, _⟩ := T_isTree
obtain ⟨v, hv⟩ := T_isTree.exists_vert_degree_one_of_nontrivial   -- leaf of T
exact ⟨v, (hT.induce_compl_singleton_of_degree_eq_one hv).mono (by tauto)⟩
```

To get **TWO** non-cut vertices, the natural lift is:
1. Take spanning tree T of G.
2. T is a tree with ≥ 4 vertices ⇒ T has at least **2** leaves z₁, z₂.
3. Both leaves are non-cut vertices of G (by lemma #8, lifted via `.mono`).

The whole construction reuses Mathlib lemmas #5, #6, #8 as-is. The single new piece is the "2 leaves" lemma (the missing row above).

---

## Proof sketch for the missing "2 leaves" lemma

**Statement** (proposed Mathlib name): `SimpleGraph.IsTree.exists_two_distinct_vert_degree_one_of_card_le_two` (or similar):

```lean
lemma IsTree.exists_two_distinct_vert_degree_one_of_two_le_card
    [Fintype V] [DecidableRel G.Adj]
    (h : G.IsTree) (hcard : 2 ≤ Fintype.card V) :
    ∃ v w : V, v ≠ w ∧ G.degree v = 1 ∧ G.degree w = 1
```

**Proof** (counting argument, ~10 lines):

By contradiction, suppose at most one vertex has degree 1. Then ≥ |V|-1 vertices have degree ≥ 2 (using `IsTree.preconnected.minDegree_pos_of_nontrivial`, every vertex has degree ≥ 1; combined with the assumption, all but possibly one have degree ≥ 2). Sum of degrees:

```
∑ v, G.degree v ≥ 2(|V| - 1) + 1 = 2|V| - 1
```

But by handshaking (lemma #15) and tree edge count (`IsTree.card_edgeFinset` gives |E| = |V| - 1):

```
∑ v, G.degree v = 2|E| = 2(|V| - 1) = 2|V| - 2
```

So `2|V| - 1 ≤ 2|V| - 2`, contradiction.

This is a direct lift of Mathlib's existing `IsTree.minDegree_eq_one_of_nontrivial` proof (Acyclic.lean:507-519) — same counting style. Estimate: **~10-20 LOC**.

---

## Three closure paths

### Path A: in-project proof (RECOMMENDED — fastest)

Add to `YangMills/ClayCore/LatticeAnimalCount.lean` (or a new helper file):

```lean
-- Helper: every nontrivial finite tree has 2 distinct degree-1 vertices.
-- (~10-20 LOC, counting argument)
private lemma _root_.SimpleGraph.IsTree.exists_two_distinct_vert_degree_one
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsTree) (hcard : 2 ≤ Fintype.card V) :
    ∃ v w : V, v ≠ w ∧ G.degree v = 1 ∧ G.degree w = 1 := by
  ... -- counting via sum_degrees_eq_twice_card_edges + IsTree.card_edgeFinset

-- Main theorem: closes B.1 via spanning tree + 2 leaves.
theorem simpleGraphHighCardTwoNonCutExists :
    SimpleGraphHighCardTwoNonCutExists := by
  intro α _ _ G hconn hcard
  classical
  obtain ⟨T, hTle, hT⟩ := hconn.exists_isTree_le
  have hcardT : 2 ≤ Fintype.card α := by linarith [hcard]
  obtain ⟨v, w, hvw, hv1, hw1⟩ :=
    hT.exists_two_distinct_vert_degree_one hcardT
  refine ⟨v, w, hvw, ?_, ?_⟩
  · exact ((hT.connected.induce_compl_singleton_of_degree_eq_one hv1).preconnected).mono (...)
  · exact ((hT.connected.induce_compl_singleton_of_degree_eq_one hw1).preconnected).mono (...)
```

**Estimated total**: 30-50 LOC (helper + main). Closes F3-COUNT B.1 immediately. Composing with v2.61 → v2.60 → v2.59 yields full safe-deletion → F3-COUNT FORMAL_KERNEL. **No external dependencies, no PR roundtrip.**

### Path B: Mathlib PR (~50-100 LOC, days-to-weeks roundtrip)

Open a Mathlib PR adding:
1. `IsTree.exists_two_distinct_vert_degree_one_of_two_le_card` (~10-20 LOC).
2. `Connected.exists_two_distinct_preconnected_induce_compl_singleton_of_card_four_le` (~20-30 LOC) — directly proves our target.

This is **strictly cleaner** than Path A (Mathlib gets the textbook lemma; future projects benefit) but blocked by `REC-MATHLIB-FORK-PR-AUTH-001` — the same authentication gap that blocks `MatrixExp_DetTrace_DimOne_PR`. Until Lluis enables `gh` auth or a reachable `lluiseriksson/mathlib4` fork, Path B cannot be initiated.

### Path C: existing Mathlib lemma (NOT viable as a single-step closure)

There is no single Mathlib lemma that directly proves `SimpleGraphHighCardTwoNonCutExists`. The closest is the SINGLE-non-cut lemma (#9 / #10), which is not enough.

The naive iteration (apply #10 twice) does not work because the second application removes a vertex from `G.induce {z₁}ᶜ`, not from `G`, so the resulting `z₂` is a non-cut of `G.induce {z₁}ᶜ`, not necessarily of `G`. The conclusion needs both `(G.induce {z_i}ᶜ).Preconnected` for `i ∈ {1, 2}` *separately*, not nested.

**Path C status**: NOT VIABLE as a one-step.

---

## Recommended closure path: **Path A (in-project proof)**

**Reasoning**:

1. **Mathlib has every primitive needed** (#1 through #15) — only the "2 leaves" counting lemma is missing.
2. **The missing lemma is ~10-20 LOC** of textbook degree-counting; no new mathematical ideas.
3. **The full closure is ~30-50 LOC** in `LatticeAnimalCount.lean`.
4. **No PR roundtrip** — Path A unblocks F3-COUNT closure immediately.
5. **Path B is strictly cleaner long-term**, but is currently blocked by `REC-MATHLIB-FORK-PR-AUTH-001`. Path A can fire now; Path B can fire later as a separate cleanup PR.

**Estimated time-to-F3-COUNT-closure via Path A**: 1 Codex commit cycle (v2.62 = `simpleGraphHighCardTwoNonCutExists` proved + B.1 closure + F3-COUNT row moves to `FORMAL_KERNEL` + lattice 28% → ~43% percentage move).

---

## Optional: minimal Mathlib PR scope (if Path B is later pursued)

For future cleanup as a separate PR (after F3-COUNT closes via Path A):

```lean
-- File: Mathlib/Combinatorics/SimpleGraph/Acyclic.lean
-- Insert after IsTree.exists_vert_degree_one_of_nontrivial (line 522-526)

/-- Every finite tree with at least two vertices has at least two distinct
vertices of degree one. -/
lemma IsTree.exists_two_distinct_vert_degree_one_of_two_le_card
    [Fintype V] [DecidableRel G.Adj] (h : G.IsTree)
    (hcard : 2 ≤ Fintype.card V) :
    ∃ v w : V, v ≠ w ∧ G.degree v = 1 ∧ G.degree w = 1 := by
  -- counting via sum_degrees + IsTree.card_edgeFinset
  ...
```

```lean
-- Insert after exists_preconnected_induce_compl_singleton_of_finite (line 570-575)

/-- A finite connected SimpleGraph with at least four vertices has two distinct
vertices that each leave the graph preconnected when removed. -/
lemma Connected.exists_two_distinct_preconnected_induce_compl_singleton_of_card_four_le
    [Finite V] (hconn : G.Connected) (hcard : 4 ≤ Nat.card V) :
    ∃ v w : V, v ≠ w ∧
      (G.induce {v}ᶜ).Preconnected ∧ (G.induce {w}ᶜ).Preconnected := by
  -- spanning tree + two leaves of tree are non-cut of G
  ...
```

**Total Mathlib PR footprint**: ~30-50 LOC across 2 lemmas. Single file change (`SimpleGraph/Acyclic.lean`). No new imports. Strong upstream-acceptance candidate.

---

## What this pre-check does NOT do

- **Does not prove** `SimpleGraphHighCardTwoNonCutExists`.
- **Does not move** F3-COUNT from `CONDITIONAL_BRIDGE`.
- **Does not move** any percentage (5% / 28% / 23-25% / 50% all preserved).
- **Does not assume** any Path will be chosen by Codex; the recommendation is informational.

---

## Honesty preservation

- F3-COUNT row: unchanged (`CONDITIONAL_BRIDGE`)
- F3-MAYER, F3-COMBINED rows: still `BLOCKED`
- All 4 percentages: unchanged at 5% / 28% / 23-25% / 50%
- Tier 2 axiom set: unchanged at 5
- This document is a **forward-looking blueprint**, not a proof artifact.

---

## Cross-references

- `YangMills/ClayCore/LatticeAnimalCount.lean:1888-1895` — open def `SimpleGraphHighCardTwoNonCutExists`
- `Mathlib/Combinatorics/SimpleGraph/Acyclic.lean:472, 507, 522, 530, 559, 570` — core Mathlib lemmas used
- `AXIOM_FRONTIER.md` v2.61.0 lines 67-77 — confirms B.1 is open and pure-graph
- `F3_COUNT_DEPENDENCY_MAP.md` lines 252-269 — "Post-v2.61 preferred subtarget" recipe
- `dashboard/mayer_mathlib_precheck.md` — sibling pre-check for F3-MAYER §(b)/B.3 BK polymer bound (analogous structure)
- `REC-CODEX-MATHLIB-LONGEST-INDUCED-PATH-CHECK-001` (RESOLVED at v2.54) — earlier successful Mathlib precheck pattern
- `REC-MATHLIB-FORK-PR-AUTH-001` — pending human action gating Path B
