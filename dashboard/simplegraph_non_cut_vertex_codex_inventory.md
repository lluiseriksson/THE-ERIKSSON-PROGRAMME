# Codex Inventory: SimpleGraph high-card non-cut theorem

**Task**: `CODEX-F3-SIMPLEGRAPH-MATHLIB-INVENTORY-001`
**Date**: 2026-04-26T14:31Z
**Status**: inventory only. No Lean theorem, ledger row, or percentage was upgraded.

## Target

The active B.1 target is the pure graph statement introduced in
`YangMills/ClayCore/LatticeAnimalCount.lean`:

```lean
def SimpleGraphHighCardTwoNonCutExists : Prop := ...
```

It is the post-v2.61 bottleneck for:

```lean
SimpleGraphHighCardTwoNonCutExists
  -> PlaquetteGraphAnchoredHighCardTwoNonCutExists
  -> PlaquetteGraphAnchoredSafeDeletionExists
  -> B.2 anchored word decoder
```

This inventory does **not** claim that the target is proved.

## Local sources checked

- Project Mathlib package:
  `C:\Users\lluis\.gemini\antigravity\scratch\THE-ERIKSSON-PROGRAMME\.lake\packages\mathlib\Mathlib`
- Separate Mathlib checkout:
  `C:\Users\lluis\Downloads\mathlib4\Mathlib`
- Project file:
  `YangMills/ClayCore/LatticeAnimalCount.lean`
- Planning files:
  `F3_COUNT_DEPENDENCY_MAP.md`,
  `dashboard/f3_decoder_iteration_scope.md`,
  `UNCONDITIONALITY_LEDGER.md`

## Candidate Mathlib artifacts found

| Artifact | File | Why it matters |
|---|---|---|
| `SimpleGraph.Connected.exists_isTree_le` | `Mathlib/Combinatorics/SimpleGraph/Acyclic.lean:463` | A connected graph has a spanning tree. This is the natural bridge from arbitrary connected graph to a tree leaf argument. |
| `SimpleGraph.Connected.exists_isTree_le_of_le_of_isAcyclic` | `Acyclic.lean:456` | Stronger spanning-tree extension from an acyclic subgraph; useful if the proof wants to preserve chosen vertices. |
| `SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial` | `Acyclic.lean:507` | A nontrivial tree has a leaf. Mathlib currently exposes one leaf, not two distinct leaves. |
| `SimpleGraph.Connected.induce_compl_singleton_of_degree_eq_one` | `Acyclic.lean:515` | Removing a degree-one vertex from a connected graph preserves connectedness. |
| `SimpleGraph.Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial` | `Acyclic.lean:546` | Existing one-non-cut-vertex theorem for finite nontrivial connected graphs, proved by spanning tree + leaf. |
| `SimpleGraph.Connected.exists_preconnected_induce_compl_singleton_of_finite` | `Acyclic.lean:556` | Existing one-preconnected-deletion theorem. This is the exact shape already used by the project for the unrooted one-delete step. |
| `SimpleGraph.Reachable.exists_isPath` | `Connectivity/Connected.lean:129` | Supplies paths from reachability; useful for local proof work around induced subgraphs and tree endpoints. |
| `SimpleGraph.IsAcyclic.induce` | `Acyclic.lean:92` | Induced subgraphs of acyclic graphs are acyclic; useful if reducing a tree after removing a leaf. |
| `SimpleGraph.isTree_iff_existsUnique_path` / `IsTree.existsUnique_path` | `Acyclic.lean:240`, `Acyclic.lean:262` | Tree path uniqueness infrastructure; possible alternative route to leaf/endpoints. |
| `SimpleGraph.isAcyclic_iff_forall_edge_isBridge` | `Acyclic.lean:173` | Edge-bridge infrastructure exists, but it is about edges, not cut vertices. |

## Candidate artifacts absent or not found

Searches over `Mathlib/Combinatorics/SimpleGraph` did **not** find a direct
vertex-cut API such as:

- `SimpleGraph.IsCutVert`
- `SimpleGraph.IsCutVertex`
- `exists_two_non_cut`
- `exists_non_cut_pair`
- `Connected.exists_two_preconnected_induce_compl_singleton`
- a theorem explicitly saying every finite connected graph with at least two
  vertices has two distinct non-cut vertices

Mathlib has `IsBridge` and edge deletion lemmas, for example
`Connected.connected_delete_edge_of_not_isBridge`, but that is edge-cut
infrastructure, not vertex-cut infrastructure.

## Interpretation

There is no obvious existing one-line theorem for
`SimpleGraphHighCardTwoNonCutExists`.

However, Mathlib already contains the key ingredients for a short in-project
proof:

1. Turn a finite connected graph into a spanning tree using
   `Connected.exists_isTree_le`.
2. Prove or derive a small missing lemma:

   ```lean
   theorem SimpleGraph.IsTree.exists_two_distinct_degree_one_of_card_ge_two
       [Fintype V] [DecidableRel T.Adj]
       (hT : T.IsTree) (hcard : 2 <= Fintype.card V) :
       exists u v, u != v /\ T.degree u = 1 /\ T.degree v = 1
   ```

   The exact statement may use `Nat.card V` or `Fintype.card V`, depending on
   the local API in `LatticeAnimalCount.lean`.
3. For each tree leaf, use the same proof pattern as
   `Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial`:
   deletion is connected in the tree, then monotone up to `G`.
4. Convert connected deletion to preconnected deletion and feed the two
   distinct candidates into `SimpleGraphHighCardTwoNonCutExists`.

The only real missing ingredient appears to be the two-leaves theorem for
finite trees, plus adapter work for the exact proposition shape.

## Recommended closure path

**Recommendation: in-project proof.**

Reason:

- Existing Mathlib is close but does not expose a direct two-non-cut theorem.
- A Mathlib PR would be reasonable later, but not required to make immediate
  project progress.
- The missing proof should be small and standard: spanning tree plus two
  distinct leaves. It is better to prove it locally first, validate the exact
  API, and only then decide whether to upstream a polished general lemma.

Expected next Codex task:

```text
CODEX-F3-SIMPLEGRAPH-HIGHCARD-PROOF-001
```

Implementation sketch for the next task:

1. Import or rely on `Mathlib.Combinatorics.SimpleGraph.Acyclic`.
2. Add a local helper near the `SimpleGraphHighCardTwoNonCutExists` block:
   a finite tree with enough vertices has two distinct leaf vertices.
3. Use `Connected.exists_isTree_le` on the subtype graph from the v2.61 target.
4. Lift the two tree leaf deletions to connected/preconnected deletions in the
   original graph.
5. Only if the complete proof compiles, compose through the v2.61/v2.60 bridges.

## Honesty check

- `F3-COUNT` remains `CONDITIONAL_BRIDGE`.
- `F3-MAYER` remains `BLOCKED`.
- `F3-COMBINED` remains `BLOCKED`.
- Planner percentages remain `5 / 28 / 23-25 / 50`.
- No new Lean code was added by this inventory.
