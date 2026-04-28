# F3 residual-fiber terminal-edge selector attempt v2.137

Task: `CODEX-F3-PROVE-TERMINAL-EDGE-SELECTOR-001`

Target:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalTerminalEdgeSelector1296
```

## Result

No Lean proof was added. The selector theorem does not close from the current
APIs without a new residual-local terminal-edge extraction theorem.

The v2.136 interface and bridge are available:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalTerminalEdgeSelector1296
physicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296_of_residualFiberCanonicalTerminalEdgeSelector1296
```

but the producer itself remains open.

## Exact Blocker

The missing theorem must take residual-local canonical path or walk evidence and
extract, for each essential parent, a terminal predecessor that:

- lies in the same residual;
- is adjacent to the essential parent when `residual.card ≠ 1`;
- supplies residual walk evidence to the target parent;
- has selected predecessor image cardinality `<= 1296` over the entire
  v2.121 bookkeeping residual fiber.

Current Lean APIs provide reachability/path existence but not this selected
terminal-edge image bound.

## Why Existing APIs Do Not Close It

`plaquetteGraphPreconnectedSubsetsAnchoredCard_root_exists_induced_path`
provides an induced residual path from the root to a target member. It does not
name or bound the image of the immediate predecessor on the terminal edge of
that path across a residual fiber.

`physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParent1296` and
`physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParent1296_reachable`
provide a bounded first-shell/root-shell parent that reaches the target. They do
not prove that this first-shell parent is adjacent to the target, and the
first-shell code is not a terminal-predecessor image bound.

`physicalPlaquetteGraph_residualDominatedTerminalPredecessorPacking1296` can
code an explicit terminal predecessor menu once `terminalPredMenu.card <= 1296`
is already supplied. It does not construct the terminal predecessor menu or its
image bound.

The local degree bound controls the neighbor set of one fixed plaquette, not the
image of selected terminal predecessors over the residual fiber.

The deleted vertex in a current safe-deletion witness is outside
`X.erase (deleted X)` and was not used as terminal-predecessor data.

Bounded finite search remains diagnostic only and was not used as proof.

## Next Structural Target

The next Lean-stable target should isolate terminal-edge extraction from an
explicit residual walk/path family, for example:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalWalkTerminalEdgeImageBound1296
```

This target should state the exact missing package: canonical residual paths for
the v2.121 bookkeeping fibers, extraction of their terminal predecessors, and a
`<= 1296` selected-image bound for those terminal predecessors. Its bridge into
`PhysicalPlaquetteGraphResidualFiberCanonicalTerminalEdgeSelector1296` should be
only a repacking bridge.

## Validation

`lake build YangMills.ClayCore.LatticeAnimalCount` passed for the current Lean
state before this note was recorded. No new theorem was introduced by this
attempt, so no new theorem-specific axiom trace was needed.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No ledger status, project percentage,
README metric, planner metric, or Clay-level claim moved.
