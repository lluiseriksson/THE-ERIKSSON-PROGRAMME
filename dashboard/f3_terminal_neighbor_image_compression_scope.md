# F3 residual terminal-neighbor image compression scope (v2.150)

Task: `CODEX-F3-TERMINAL-NEIGHBOR-IMAGE-COMPRESSION-SCOPE-001`

## Result

Scoped the sharper residual-fiber compression target:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborImageCompression1296
```

with intended bridge:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296_of_residualFiberTerminalNeighborImageCompression1296
```

Bridge conclusion:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296
```

No Lean file was edited for this scope.

## Proposed Shape

The compression theorem should quantify over the same v2.121 bookkeeping fiber
data consumed by
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296`:
`root`, `k`, `deleted`, `parentOf`, `essential`, plus the choice/image/subset
bookkeeping hypotheses.

For each residual fiber, it should produce residual-only data:

```lean
terminalNeighborMenu :
  Finset (ConcretePlaquette physicalClayDimension L) →
    Finset (ConcretePlaquette physicalClayDimension L)

terminalNeighborOfParent :
  ∀ residual,
    (p : {p : ConcretePlaquette physicalClayDimension L //
      p ∈ essential residual}) →
      {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}
```

with the proof obligations:

* `terminalNeighborMenu residual ⊆ residual`;
* `(terminalNeighborMenu residual).card ≤ 1296`;
* every selected `terminalNeighborOfParent residual p` lies in
  `terminalNeighborMenu residual`;
* each selected terminal neighbor carries
  `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData residual p.1 ...`;
* the selected image is covered by the menu:

```lean
((essential residual).attach.image
  (fun p => (terminalNeighborOfParent residual p).1))
    ⊆ terminalNeighborMenu residual
```

The bridge then proves the existing selector-image interface by reusing the
selector and evidence, and deriving the image-cardinality bound from
`Finset.card_le_card` applied to `image ⊆ terminalNeighborMenu residual`,
followed by `(terminalNeighborMenu residual).card ≤ 1296`.

## Why This Is Sharper Than v2.148

`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296`
requires a selector and directly asks for the selected-image cardinality bound.
The compression theorem isolates the missing construction: a residual-local
bounded terminal-neighbor menu that dominates the selected image.

This is not merely repackaging the v2.148 interface. The new theorem must build
or structurally name the bounded menu before the selector-image bound is
available.

## Non-Substitutes

The selected-image compression is not supplied by:

* local neighbor existence for each parent, which gives pointwise choices but no
  global image bound;
* residual path existence or first-edge/terminal path splitting, which gives
  connectivity but no bounded selected image;
* root or root-shell reachability, which concerns first-shell data from the root
  rather than terminal neighbors adjacent to arbitrary essential parents;
* local degree of one fixed plaquette, which does not bound the image of a
  selector over an entire residual fiber;
* residual size or raw residual frontier growth, which may be much larger than
  `1296`;
* deleted-vertex adjacency outside the residual, which is not terminal-neighbor
  data inside the residual;
* empirical bounded search, which is not proof;
* packing an already bounded menu, which can code a menu only after the
  cardinality bound has been proved.

## Stop-Condition Check

This scope does not choose terminal neighbors post-hoc from a current
`(X, deleted X)` witness. The terminal-neighbor menu must be residual-only and
fiber-produced.

It does not claim decoder compression, F3-COUNT progress, or any status or
percentage move.

## Validation

Dashboard-only scope. No Lean file was edited, so no `lake build` was required.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, or Clay-level claim moved.

## Next Task

Add the Lean interface and projection bridge:

```text
CODEX-F3-TERMINAL-NEIGHBOR-IMAGE-COMPRESSION-INTERFACE-001
```
