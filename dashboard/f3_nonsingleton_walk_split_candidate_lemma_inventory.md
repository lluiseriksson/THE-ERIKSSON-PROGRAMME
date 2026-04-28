# F3 Non-Singleton Walk-Split Candidate Lemma Inventory

Task: `CODEX-F3-NONSINGLETON-WALK-SPLIT-CANDIDATE-LEMMA-INVENTORY-001`
Status: `DONE_INVENTORY_EXACT_BLOCKER`
Date: 2026-04-28T00:50:00Z

## Target

The downstream missing source theorem is
`PhysicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296`.
Its role is to supply the residual induced-graph burden needed by
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296`:
for every v2.121 bookkeeping residual fiber and essential parent, the
singleton case is vacuous, while the non-singleton case must provide a
residual terminal neighbor adjacent to the parent together with compatible
induced residual walks source-to-parent, source-to-terminalNeighbor, and
terminalNeighbor-to-parent.

## Candidate Lean Lemma Map

1. `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`
   (`YangMills/ClayCore/LatticeAnimalCount.lean:3364`)

   This is the record that the walk-split theorem ultimately has to build.
   It requires a residual `target`, `source`, induced residual `canonicalWalk`,
   `prefixToTerminalNeighbor`, `terminalNeighborSuffix`, a final-edge condition
   `p ∈ neighborFinset terminalNeighbor.1` for non-singleton residuals, and a
   `terminalNeighborCode : Fin 1296`.

2. `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296`
   (`YangMills/ClayCore/LatticeAnimalCount.lean:4878`)

   This is the immediate downstream proposition. It already packages the
   source, target, terminalNeighbor, terminalNeighborCode, three induced
   residual walks, and the non-singleton final-edge adjacency. The bridge
   `physicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296_of_residualFiberTerminalNeighborSelectorDataSource1296`
   repacks this data into the domination relation.

3. `plaquetteGraphPreconnectedSubsetsAnchoredCard_root_reachable`
   (`YangMills/ClayCore/LatticeAnimalCount.lean:7671`)

   Candidate role: once both endpoints are known to lie in the same anchored
   residual, this supplies induced residual reachability from the root/source
   side to a member. It can support the source-to-parent and
   source-to-terminalNeighbor walk obligations after a residual terminal
   neighbor has already been found.

   Insufficiency: it does not produce a residual neighbor `q` adjacent to an
   arbitrary essential parent `p`, and residual paths alone are not selector
   data.

4. `plaquetteGraphPreconnectedSubsetsAnchoredCard_root_exists_induced_path`
   (`YangMills/ClayCore/LatticeAnimalCount.lean:7688`)

   Candidate role: path-form version of the previous reachability lemma, useful
   for constructing `Nonempty` induced residual walks once endpoints are known.

   Insufficiency: it still does not provide the non-singleton final-edge
   adjacency `p ∈ neighborFinset q` with `q ∈ residual`.

5. v2.121 bookkeeping residual facts used by the selector-data interfaces

   Candidate role: the hypotheses around the v2.121 residual fiber give
   `p ∈ essential residual`, the essential-subset map into `residual`, and the
   deleted-witness bookkeeping needed to set `target := p`.

   Insufficiency: these facts identify the essential parent as a residual
   member, but do not by themselves give a distinct or adjacent residual
   terminal neighbor in the non-singleton case.

6. `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent`
   (`YangMills/ClayCore/LatticeAnimalCount.lean:7038`)

   Candidate role: this is relevant only to the older deletion-parent
   construction: for a deleted vertex `z`, it finds a parent in `X.erase z`
   adjacent to `z`.

   Blocker: this is the wrong direction for the current theorem. The deleted
   vertex is not an element of `residual = X.erase (deleted X)`, so it cannot be
   used as the residual `terminalNeighbor`. This lemma cannot prove the needed
   final-edge adjacency from a residual `q` to an essential parent `p`.

7. Root-shell and root-neighbor helpers listed near the axiom trace block
   (`...exists_root_neighborFinset_to_member`,
   `...exists_root_neighborFinset_tail_to_member`,
   `...exists_root_neighborFinset_reachable_to_member`,
   and physical root-shell code variants)

   Candidate role: these may help choose root-relative predecessors or paths in
   anchored buckets.

   Insufficiency: root-shell reachability and root-relative codes do not prove
   that every essential parent in a non-singleton residual has a residual
   adjacent terminal neighbor.

## Exact Blocker

The missing Lean ingredient is a non-cardinality graph lemma for induced
residuals:

```lean
-- Tentative shape, not yet present.
plaquetteGraphPreconnectedSubsetsAnchoredCard_nonSingleton_member_has_neighbor
  (hresidual : residual ∈
    plaquetteGraphPreconnectedSubsetsAnchoredCard physicalClayDimension L root (k - 1))
  (hp : p ∈ residual)
  (hcard : residual.card ≠ 1) :
  ∃ q, q ∈ residual ∧ p ∈ (plaquetteGraph physicalClayDimension L).neighborFinset q
```

After this neighbor lemma exists, `root_reachable` or
`root_exists_induced_path` can plausibly build the needed induced residual
walks. Without it, the current file has reachability tools but no Lean-stable
source for the non-singleton final-edge residual adjacency.

## Rejected Routes

This inventory does not use selected-image cardinality, bounded menu
cardinality, `finsetCodeOfCardLe`, empirical search, deleted-vertex adjacency
outside the residual, residual size alone, residual paths alone, root-shell
reachability alone, local degree alone, local displacement codes,
parent-relative `terminalNeighborCode` equality, or the v2.161 circular chain.

F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric,
planner metric, ledger row, or Clay-level claim moved.
