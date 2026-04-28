# F3 residual-fiber canonical last-edge image interface v2.132

Task: `CODEX-F3-RESIDUAL-FIBER-CANONICAL-LAST-EDGE-IMAGE-INTERFACE-001`

## Result

Added the no-sorry Lean Prop/interface:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:3419
```

The interface is indexed by the same v2.121 base-aware bookkeeping data as
`PhysicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296`, but it
requires canonical residual last-edge data first:

```lean
canonicalLastEdgeData residual p :
  PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgeData residual p.1
```

It separately records:

- last-edge adjacency for non-singleton residual fibers, using the
  `predecessor` field of the canonical datum;
- selected predecessor image cardinality `<= 1296`.

This is not a restatement of v2.129.  The new interface exposes canonical
target, target equality, residual predecessor, induced residual walk, and
`Fin 1296` code data before projecting a terminal-predecessor selector.

## Bridge Status

The requested bridge target is:

```lean
physicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296_of_residualFiberCanonicalLastEdgeImageBound1296
```

I attempted the projection bridge.  The term typechecked, but its
`#print axioms` trace included:

```text
[propext, sorryAx, Classical.choice, Quot.sound]
```

Because the validation frontier allows no `sorryAx`, the bridge theorem was not
left in Lean.  This triggers the listed stop condition for the bridge, while
still allowing the Prop/interface itself to land.

## Non-Confusions

The interface does not use deleted-vertex adjacency outside the residual as
terminal-predecessor data.

It does not treat root reachability, local degree, raw residual frontier growth,
or residual size as the selected-image bound.

It does not use empirical bounded-search evidence.

## Validation

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

passed after the interface-only Lean edit.

No new theorem was left in Lean, so there is no new theorem axiom trace to
audit.  The rejected bridge attempt is documented above because its trace would
have exceeded the allowed frontier.

The new Prop/interface itself has axiom trace:

```text
[propext, Classical.choice, Quot.sound]
```

## Next Exact Blocker

The next task should either:

1. identify why the projection bridge's attempted axiom trace includes
   `sorryAx`; or
2. prove a version of the bridge whose statement avoids the `sorryAx` dependency
   while still projecting canonical last-edge data into
   `PhysicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296`.

Recommended next task:

```text
CODEX-F3-CANONICAL-LAST-EDGE-BRIDGE-AXIOM-FRONTIER-001
```

## Non-Claims

This task does not prove:

- `PhysicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296`;
- `PhysicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296`;
- the projection bridge into v2.129;
- any decoder theorem or compression to older constants.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No ledger status, project percentage,
README metric, planner metric, or Clay-level claim moved.
