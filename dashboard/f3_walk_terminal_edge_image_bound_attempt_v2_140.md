# F3 walk terminal-edge selected-image bound attempt (v2.140)

Task: `CODEX-F3-PROVE-WALK-TERMINAL-EDGE-IMAGE-BOUND-001`

## Result

Attempted to prove:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalWalkTerminalEdgeImageBound1296
```

No Lean proof was added. The current API stack does not yet supply the
selected terminal-predecessor image bound required by the v2.139 interface.

## Exact no-closure blocker

The next missing theorem is a sharper residual-local terminal-suffix image
statement, tentatively:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixImageBound1296
```

It should bridge into:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalWalkTerminalEdgeImageBound1296
```

The missing content is not ordinary reachability. For each v2.121 bookkeeping
residual fiber and essential parent, it must provide:

- a residual-local canonical walk/path source, chosen from residual data rather
  than from the current `(X, deleted X)` witness;
- terminal-suffix extraction, including the immediate predecessor on the final
  residual edge to the essential parent;
- last-edge adjacency and residual suffix evidence inside the residual;
- a selected terminal-predecessor image-cardinality proof `<= 1296`.

## Existing APIs checked

The available path and reachability helpers are insufficient for this target:

- `plaquetteGraphPreconnectedSubsetsAnchoredCard_root_exists_induced_path`
  proves induced-path existence, but does not select a bounded terminal
  predecessor image over a residual fiber.
- `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296_tail_to_member`
  and
  `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParent1296_reachable`
  are first-shell/root-shell reachability tools, not terminal-edge selected-image
  bounds.
- `simpleGraph_walk_exists_adj_start_of_ne` and
  `simpleGraph_walk_exists_adj_start_and_tail_of_ne` can expose first-edge data
  from a walk. Reversal or suffix extraction may help with pure terminal-edge
  bookkeeping, but it still would not prove the selected predecessor image has
  cardinality `<= 1296`.
- `plaquetteWalk_card_le_physical_ternary` gives walk-count growth of the form
  `1296 ^ n`, not a one-symbol selected terminal-predecessor image bound.
- The v2.124 packing theorem encodes an already bounded explicit menu. It does
  not construct that menu or prove the image bound.

Using deleted-vertex adjacency outside the residual as terminal-predecessor data
is forbidden and was not used.

## Non-confusions

This attempt does not treat path existence, root/root-shell reachability, local
degree of one plaquette, residual size, raw residual frontier growth, empirical
bounded search, or packing of an already bounded menu as proof of the selected
terminal-predecessor image bound.

## Validation

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

passed for the current Lean state. No new theorem was introduced by this attempt,
so no new theorem-specific axiom trace was needed.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, or Clay-level claim moved.

## Next task

Scope the sharper theorem:

```text
CODEX-F3-TERMINAL-SUFFIX-IMAGE-BOUND-SCOPE-001
```

The scope should isolate residual-local canonical walk/path source selection,
terminal-suffix extraction, and selected terminal-predecessor image-cardinality
`<= 1296`, then name the bridge into
`PhysicalPlaquetteGraphResidualFiberCanonicalWalkTerminalEdgeImageBound1296`.
