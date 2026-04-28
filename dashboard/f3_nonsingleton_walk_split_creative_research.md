# F3 non-singleton residual walk-split creative research

Task: `CODEX-F3-NONSINGLETON-WALK-SPLIT-CREATIVE-RESEARCH-001`  
Status: `DONE_RESEARCH_SUPERSEDED_BY_EXISTING_V2_192_PROOF`  
Date: 2026-04-27T23:25:31Z

## Scope

This is a research/scoping note for
`PhysicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296`.
It records non-circular theorem formulations and proof routes for the residual
induced-graph walk-split burden isolated by v2.187.

The current Lean file already contains the downstream closure:

```lean
physicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296 :
  PhysicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296

physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296_of_residualFiberNonSingletonMemberNeighborWalkSplit1296 :
  PhysicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296 →
  PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296
```

Accordingly, this note is retrospective/auditable research.  It does not add a
new theorem, does not claim a new proof closure, and does not move F3-COUNT.

## Route A: p-as-source one-edge split (dominant, already landed)

Formulation:

```lean
PhysicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296
```

with:

- `source = p`;
- `target = p`;
- singleton residual case using `terminalNeighbor = target` and nil walks;
- non-singleton residual case using
  `PhysicalPlaquetteGraphResidualFiberNonSingletonMemberHasResidualNeighbor1296`
  only as the final-edge adjacency source;
- induced one-edge walks `p -> terminalNeighbor` and
  `terminalNeighbor -> p` from the residual adjacency.

Why this is non-circular:

- It builds the source and target residual subtypes explicitly.
- It provides all three induced residual walk witnesses.
- The residual neighbor theorem supplies only final-edge adjacency, not the
  whole selector-data source.
- The deleted vertex is never used as a residual terminal neighbor for
  `residual = X.erase (deleted X)`.

Lean support:

- `PhysicalPlaquetteGraphResidualFiberNonSingletonMemberHasResidualNeighbor1296`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:5478`);
- `physicalPlaquetteGraphResidualFiberNonSingletonMemberHasResidualNeighbor1296`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:5533`);
- `PhysicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:5563`);
- `physicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:5636`);
- bridge to selector-data source at
  `YangMills/ClayCore/LatticeAnimalCount.lean:5786`.

If replayed on a stale branch, the exact blockers are the residual-member
neighbor theorem and the packaging step that extracts a current witness from
`essential residual = image parentOf ...` to recover the residual anchored
family hypothesis.

## Route B: generic first-edge induced-walk split

Candidate theorem shape:

```lean
∀ X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard physicalClayDimension L root n,
  p ∈ X → X.card ≠ 1 →
    ∃ q : {q // q ∈ X},
      p ∈ (plaquetteGraph physicalClayDimension L).neighborFinset q.1 ∧
      Nonempty (((plaquetteGraph physicalClayDimension L).induce {x | x ∈ X}).Walk
        ⟨p, hp⟩ ⟨q.1, q.2⟩) ∧
      Nonempty (((plaquetteGraph physicalClayDimension L).induce {x | x ∈ X}).Walk
        ⟨q.1, q.2⟩ ⟨p, hp⟩)
```

Route:

1. use non-singleton plus `p ∈ residual` to find a distinct residual member;
2. use induced preconnectedness of the anchored residual to obtain a nontrivial
   induced residual walk;
3. use `simpleGraph_walk_exists_adj_start_of_ne` or
   `simpleGraph_walk_exists_adj_start_and_tail_of_ne` to extract the first
   residual edge;
4. convert induced adjacency into the two one-edge induced walks needed by the
   selector-data source package.

Why this is non-circular:

- The theorem is about induced residual graph structure, not cardinality of a
  selected image or menu.
- It still must package source/target subtypes and induced walks; it does not
  treat residual-neighbor existence alone as full selector data.
- It does not use deleted-vertex adjacency outside the residual.

Lean support:

- `simpleGraph_walk_exists_adj_start_of_ne`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:1369`);
- `simpleGraph_walk_exists_adj_start_and_tail_of_ne`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:1382`);
- `plaquetteGraphPreconnectedSubsetsAnchoredCard_nonSingleton_member_has_neighbor`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:1395`).

Exact blocker if not using Route A directly: prove and package the two induced
one-edge walks alongside the neighbor extraction, instead of only returning an
ambient neighborFinset fact.

## Route C: anchored-source/root-source split

Candidate theorem shape:

```lean
∀ residual ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard physicalClayDimension L root (k - 1),
  p ∈ essential residual →
  residual.card ≠ 1 →
    ∃ source target terminalNeighbor,
      source.1 = root ∧ target.1 = p ∧
      Nonempty (residual-induced Walk source target) ∧
      Nonempty (residual-induced Walk source terminalNeighbor) ∧
      Nonempty (residual-induced Walk terminalNeighbor target) ∧
      p ∈ neighborFinset terminalNeighbor.1
```

Route:

1. use anchored residual membership to set `source = root`;
2. use `essential residual ⊆ residual` for `target = p`;
3. use Route B or the neighbor-only theorem to get `terminalNeighbor`;
4. use residual preconnectedness for `root -> p` and `root -> terminalNeighbor`;
5. use the one-edge residual adjacency for `terminalNeighbor -> p`.

Why this is non-circular:

- It separates walk construction from final-edge neighbor existence.
- It still constructs all source/target subtypes and induced residual walks.
- It does not rely on selected-image cardinality, menu cardinality, empirical
  search, or `finsetCodeOfCardLe`.

Exact blockers:

- expose the root membership of every anchored residual as a reusable lemma;
- make the residual-induced walks from `root` proof-relevant enough to fit the
  `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` payload;
- keep the terminal-neighbor final edge inside the residual, not at the deleted
  vertex outside `X.erase (deleted X)`.

## Route D: v2.121 bookkeeping witness unpacking route

Candidate theorem shape:

```lean
PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296 →
PhysicalPlaquetteGraphResidualFiberNonSingletonMemberNeighborWalkSplit1296
```

Route:

1. unpack the v2.121 `essential residual = image parentOf ...` clause to obtain
   a current witness `X` only for proving that the residual is an anchored
   `(k - 1)` member;
2. use `essential residual ⊆ residual` to place `p` inside the residual;
3. delegate the non-singleton final edge to Route A/B;
4. package induced residual walks without using the deleted vertex as a
   terminal neighbor.

Why this is non-circular:

- The current witness is used only to recover the residual-fiber anchored
  hypothesis and `2 ≤ k`, not to choose a post-hoc terminal neighbor from the
  deleted vertex.
- The terminal neighbor remains a residual subtype member.
- No selected-image or menu-cardinality code is introduced.

Lean support:

- `PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:6857`);
- `physicalPlaquetteGraph_baseAwareTerminalPredecessorBookkeeping1296`
  (`YangMills/ClayCore/LatticeAnimalCount.lean:8379`).

## Explicit non-routes

All routes above reject:

- treating residual-neighbor existence alone as selector-data source;
- using deleted `X` as a residual terminal neighbor for
  `residual = X.erase (deleted X)`;
- selected-image cardinality;
- bounded menu cardinality;
- `finsetCodeOfCardLe`;
- empirical search;
- residual paths alone without source/target subtype and split-walk payload;
- root-shell reachability alone;
- local degree alone;
- local displacement or parent-relative `terminalNeighborCode` equality;
- the v2.161 selector-image cycle.

## Validation

- This dashboard note records four candidate routes, including the dominant
  route already present in Lean.
- F3-COUNT remains `CONDITIONAL_BRIDGE`; no percentage, status, README metric,
  planner metric, ledger row, proof claim, or Clay-level claim moved.
