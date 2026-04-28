# F3 residual terminal-neighbor selector image scope (v2.147)

Task: `CODEX-F3-TERMINAL-NEIGHBOR-SELECTOR-IMAGE-SCOPE-001`

## Result

Scoped a sharper Lean-stable target:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296
```

This target is intended to feed the existing v2.145 canonical terminal-neighbor
interface through the projection bridge:

```lean
physicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborImageBound1296_of_residualFiberTerminalNeighborSelectorImageBound1296
```

with conclusion:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborImageBound1296
```

No Lean file was edited in this scope pass.

## Proposed Contract

The selector theorem should quantify over the same v2.121 base-aware
bookkeeping residual fibers used by
`PhysicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborImageBound1296`.
For each residual fiber and each essential parent inside that fiber it should
provide a residual-local selected terminal neighbor:

```lean
terminalNeighborOfParent :
  ∀ residual,
    (p : {p // p ∈ essential residual}) →
      {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}
```

The evidence attached to this selector should include:

* the selected `q` lies in the same residual as the essential parent `p`;
* in the non-singleton branch, `p.1 ∈ plaquetteGraph_neighborFinset q.1`;
* residual-local canonical walk/path or suffix evidence connecting the selected
  terminal neighbor to the essential parent inside the residual;
* no use of deleted-vertex adjacency outside the residual as terminal-neighbor
  data;
* a selected-image cardinality bound

```lean
∀ residual,
  ((essential residual).attach.image
    (fun p => (terminalNeighborOfParent residual p).1)).card ≤ 1296
```

Optionally the data can be packaged in a structure such as:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
```

whose fields are then projected into
`PhysicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborData`.

## Bridge Shape

The bridge

```lean
physicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborImageBound1296_of_residualFiberTerminalNeighborSelectorImageBound1296
```

should be projection-only. It should build
`PhysicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborData` by copying the
selector output and residual-local terminal-neighbor evidence from the sharper
selector theorem, then carry the selected-image `<= 1296` bound unchanged.

This bridge must not prove the selected-image bound from residual path
existence, local degree, residual size, raw frontier growth, or packing of an
already bounded menu. Those are non-substitutes for the selector image theorem.

## Non-Substitutes

The scoped theorem is distinct from:

* residual path existence or first-edge path splitting, which gives connectivity
  evidence but not a bounded selected terminal-neighbor image;
* root/root-shell reachability, which is first-shell data and not terminal-edge
  adjacency inside the residual;
* local degree bounds for one fixed plaquette, which do not bound the image of a
  selector over all essential parents in a residual fiber;
* residual size or raw residual frontier growth;
* deleted-vertex adjacency, since the deleted vertex lies outside the residual;
* packing an already bounded menu, which can encode a menu after it exists but
  does not construct the residual-local selector or its image bound.

## Validation

This was a dashboard-only scope artifact. No Lean file was edited, so no
`lake build` was required for this task. `F3-COUNT` remains
`CONDITIONAL_BRIDGE`; no status, percentage, README metric, planner metric, or
Clay-level claim moved.

## Next Task

Add the Lean interface:

```text
CODEX-F3-TERMINAL-NEIGHBOR-SELECTOR-IMAGE-INTERFACE-001
```

