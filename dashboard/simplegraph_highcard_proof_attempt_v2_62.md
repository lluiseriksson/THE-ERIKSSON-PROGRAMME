# v2.62 Codex proof attempt: SimpleGraphHighCardTwoNonCutExists

**Task**: `CODEX-F3-SIMPLEGRAPH-HIGHCARD-PROOF-001`
**Date**: 2026-04-26T14:45Z
**Status**: PARTIAL / no Lean theorem added.

## Target

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

## Attempted route

The most promising route remains:

1. Use Mathlib's `Connected.exists_isTree_le` to obtain a spanning tree
   `T ≤ G`.
2. Produce two distinct leaves `z₁ z₂` of `T`.
3. Use `Connected.induce_compl_singleton_of_degree_eq_one` on the tree to get
   connectedness after deleting each leaf.
4. Use monotonicity from `T ≤ G` to obtain the two preconnected deletion
   witnesses in `G`.

This route is mathematically standard and avoids iterating the one-non-cut
lemma in an invalid way.

## Why the one-non-cut lemma is not enough

Mathlib already has:

```lean
Connected.exists_preconnected_induce_compl_singleton_of_finite
```

Applying it twice is not sufficient. If the second deletion is found only in
`G.induce {z₁}ᶜ`, it does not automatically imply that deleting the second
vertex from the original `G` leaves `z₁` connected to the rest. The spanning
tree/two-leaf route avoids this failure because each candidate is a leaf of
the same spanning tree of the original graph.

## Exact remaining theorem

The proof now reduces to a small but real finite-tree lemma:

```lean
theorem SimpleGraph.IsTree.exists_two_distinct_degree_one_of_card_ge_two
    {V : Type} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    (hT : T.IsTree) (hcard : 2 ≤ Fintype.card V) :
    ∃ z₁ z₂ : V, z₁ ≠ z₂ ∧ T.degree z₁ = 1 ∧ T.degree z₂ = 1
```

For the current `SimpleGraphHighCardTwoNonCutExists` target, `hcard` can be
weakened/strengthened as convenient; the caller has `4 ≤ Fintype.card α`.

## Mathlib support already available

- `Connected.exists_isTree_le`
- `IsTree.exists_vert_degree_one_of_nontrivial`
- `Connected.induce_compl_singleton_of_degree_eq_one`
- `Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial`
- `Connected.exists_preconnected_induce_compl_singleton_of_finite`
- `Preconnected.mono` / `Connected.mono`
- `IsAcyclic.induce`

## Recommendation

Create a focused Codex task for the two-leaves lemma. The likely proof is by
degree-sum counting:

- In a nontrivial tree, every vertex has positive degree.
- If there are not two distinct degree-one vertices, all but at most one vertex
  have degree at least two.
- Then the degree sum is at least `2 * |V| - 1`, contradicting the tree identity
  `sum_degrees = 2 * (|V| - 1)`.

This is an in-project proof first. Once stable, it may be a good small Mathlib
PR candidate.

## Honesty status

- `SimpleGraphHighCardTwoNonCutExists` is still **open**.
- `F3-COUNT` remains `CONDITIONAL_BRIDGE`.
- `F3-MAYER` and `F3-COMBINED` remain `BLOCKED`.
- Planner percentages remain `5 / 28 / 23-25 / 50`.
- No `sorry`, new axiom, or Lean theorem was introduced by this attempt.
