# F3 residual terminal-neighbor selector-data source scope/interface v2.186

Task: `CODEX-F3-TERMINAL-NEIGHBOR-SELECTOR-DATA-SOURCE-SCOPE-001`

Status: `DONE_INTERFACE_AND_BRIDGE_LANDED_NO_STATUS_MOVE`

## Lean landing

Added the full residual-local selector-data source interface:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorDataSource1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:4878
```

The interface is deliberately stronger than a residual-neighbor existence
lemma.  For each v2.121 bookkeeping residual fiber and essential parent it
exposes:

- `source : {s // s ∈ residual}`;
- `target : {r // r ∈ residual}`;
- `terminalNeighbor : {q // q ∈ residual}`;
- `terminalNeighborCode : Fin 1296`;
- `target.1 = p.1`;
- an induced residual walk `source -> target`;
- an induced residual walk `source -> terminalNeighbor`;
- an induced residual walk `terminalNeighbor -> target`;
- final-edge adjacency from `terminalNeighbor` to the parent when
  `residual.card ≠ 1`.

This is the structural package needed to build:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
```

## Bridge landed

Added the no-sorry bridge:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296_of_residualFiberTerminalNeighborSelectorDataSource1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:5000
```

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296
```

The proof repackages the exposed source/target/terminal-neighbor/walk/code
fields into `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`
and returns the selected terminal neighbor as the domination witness.

## Why this sharpens v2.185

The v2.185 proof attempt showed that Cowork's Strategy A cannot close from a
bare lemma such as:

```lean
essential_parent_has_residual_neighbor
```

Such a lemma might give an element of
`neighborFinset p.1 ∩ residual`, but the actual target needs the full selector
record: the source vertex, target equality, canonical residual walk, prefix to
the terminal neighbor, terminal-neighbor suffix, final-edge adjacency, and a
`Fin 1296` code.

This v2.186 interface is therefore the correct upstream theorem to prove next.
It is smaller than the domination relation in proof structure because it names
the actual selector-data components that must be constructed, but it is stronger
than local adjacency alone.

## Explicit non-routes

The interface and bridge do not use:

- residual-neighbor existence alone as selector data;
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

## Validation

Command:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result: passed.

The new bridge axiom trace is:

```text
YangMills.physicalPlaquetteGraphResidualFiberTerminalNeighborDominationRelation1296_of_residualFiberTerminalNeighborSelectorDataSource1296:
  [propext, Classical.choice, Quot.sound]
```

F3-COUNT remains `CONDITIONAL_BRIDGE`; no percentage, status, README metric,
planner metric, ledger row, or Clay-level claim moved.

## Next Codex task

```text
CODEX-F3-PROVE-TERMINAL-NEIGHBOR-SELECTOR-DATA-SOURCE-001
```
