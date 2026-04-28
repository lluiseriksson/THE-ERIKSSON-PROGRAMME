# F3 residual terminal-neighbor domination relation scope/interface v2.184

Task: `CODEX-F3-TERMINAL-NEIGHBOR-DOMINATION-RELATION-SCOPE-001`

Status: `DONE_INTERFACE_AND_BRIDGE_LANDED_NO_STATUS_MOVE`

## Lean landing

Added the menu-free residual terminal-neighbor domination relation:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:4880
```

The interface is deliberately weaker than:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296
```

It asks only for the domination relation needed by the selector source:

```lean
∀ residual,
  (p : {p : ConcretePlaquette physicalClayDimension L //
    p ∈ essential residual}) →
    ∃ q : {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
      Nonempty
        (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
          residual p.1 q)
```

This is intentionally an existence relation, not an already-chosen selector
function.  The bridge below performs the structural choice once and packages the
selector source.

## Bridge landed

Added the no-sorry bridge:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296_of_residualFiberTerminalNeighborDominationRelation1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:4930
```

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296
```

The proof chooses the residual terminal neighbor supplied by the relation for
each residual fiber and essential parent, then extracts the corresponding
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` from the
`Nonempty` witness.

## Why this is the v2.183 sharpened blocker

The v2.183 reduction showed that
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296` follows
from the domination-relation part of
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296`, while
ignoring the menu-cardinality field.  This v2.184 interface makes that smaller
source explicit.

The next proof burden is therefore:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296
```

not a bounded menu, selected-image bound, or selector-code separation theorem.

## Explicit non-routes

The interface and bridge do not use:

- bounded menu cardinality;
- selected-image cardinality;
- `finsetCodeOfCardLe` on an already bounded selected image;
- the v2.161 cycle
  `SelectorImageBound -> SelectorCodeSeparation -> CodeSeparation ->
   DominatingMenu -> ImageCompression -> SelectorImageBound`;
- residual paths alone;
- root-shell reachability alone;
- local degree;
- residual size;
- raw frontier;
- deleted-vertex adjacency alone;
- local displacement codes;
- parent-relative `terminalNeighborCode` equality;
- empirical bounded search;
- post-hoc terminal-neighbor choices from a current witness.

## Cowork alignment

Cowork's concurrent brainstorm:

```text
dashboard/f3_terminal_neighbor_domination_relation_brainstorm_v2_184.md
```

recommended exactly this interface shape and proposed Strategy A as the primary
next proof route: a canonical lex-min residual neighbor selector, with first
blocker `essential_parent_has_residual_neighbor`.

## Validation

Command:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: passed.

The new bridge axiom trace is:

```text
YangMills.physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorSource1296_of_residualFiberTerminalNeighborDominationRelation1296:
  [propext, Classical.choice, Quot.sound]
```

F3-COUNT remains `CONDITIONAL_BRIDGE`; no percentage, status, README metric,
planner metric, ledger row, or Clay-level claim moved.

## Next Codex task

```text
CODEX-F3-PROVE-TERMINAL-NEIGHBOR-DOMINATION-RELATION-001
```
