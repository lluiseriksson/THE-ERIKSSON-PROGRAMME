# F3 residual canonical terminal-neighbor image bound scope (v2.144)

Task: `CODEX-F3-TERMINAL-NEIGHBOR-IMAGE-BOUND-SCOPE-001`

## Result

Scoped the next Lean-stable producer target:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborImageBound1296
```

with intended projection bridge:

```lean
physicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixImageBound1296_of_residualFiberCanonicalTerminalNeighborImageBound1296
```

and bridge conclusion:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixImageBound1296
```

No Lean file was edited in this scope pass.

## Proposed contract

The target should quantify over the same v2.121 base-aware bookkeeping residual
fibers used by `PhysicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixImageBound1296`.
For each residual fiber and each essential parent `p`, it should provide
residual-local terminal-neighbor data, separated from the final suffix repacking:

- `target : {r // r ∈ residual}` with `target_eq : target.1 = p`;
- `source : {s // s ∈ residual}` and a residual-local canonical walk/path from
  `source` to `target`;
- `terminalNeighbor : {q // q ∈ residual}`;
- residual-local prefix evidence from `source` to `terminalNeighbor`;
- last-edge adjacency evidence, for non-singleton residual fibers, that
  `p ∈ neighborFinset terminalNeighbor.1`;
- residual-local suffix evidence from `terminalNeighbor` to `target`;
- a `Fin 1296` code for the selected `terminalNeighbor`;
- the load-bearing image bound
  `((essential residual).attach.image
    (fun p => (terminalNeighborData residual p).terminalNeighbor.1)).card ≤ 1296`.

The image bound is the new mathematical content. The bridge into the terminal
suffix theorem should only rename `terminalNeighbor` as the terminal predecessor
field and repack the prefix/suffix/last-edge evidence into
`PhysicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixData`.

## Bridge shape

The bridge should be projection-only:

```lean
theorem physicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixImageBound1296_of_residualFiberCanonicalTerminalNeighborImageBound1296
    (h :
      PhysicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborImageBound1296) :
    PhysicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixImageBound1296 := by
  -- obtain terminalNeighborData and the selected-image bound from h
  -- build PhysicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixData
  -- by copying target/source/canonicalWalk/prefix/suffix/code fields
  -- and using terminalNeighbor as terminalPred
```

No post-hoc choice from a current `(X, deleted X)` witness is allowed in this
bridge. The selector must already be residual-indexed.

## Non-confusions

This target is not merely residual path existence or path splitting. Such data
may supply the prefix and suffix shape, but it does not prove the selected
terminal-neighbor image has cardinality `<= 1296`.

It is not root/root-shell reachability. Root-shell APIs can name first-shell
parents, but the selected neighbor here must be terminal-adjacent to the
essential parent inside the residual.

It is not local degree, residual size, raw residual frontier growth, or packing
of an already bounded menu. Those are different bounds and do not construct the
selected terminal-neighbor image.

It must not use deleted-vertex adjacency outside the residual as terminal
predecessor data.

## Validation

Dashboard-only scope artifact created. No Lean file was edited, so no new
theorem-specific axiom trace or `lake build` was required for this step.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, or Clay-level claim moved.

## Next task

Add the no-sorry Lean interface and projection bridge if safe:

```text
CODEX-F3-TERMINAL-NEIGHBOR-IMAGE-BOUND-INTERFACE-001
```
