# F3 residual canonical terminal-suffix image bound attempt (v2.143)

Task: `CODEX-F3-PROVE-TERMINAL-SUFFIX-IMAGE-BOUND-001`

## Result

Attempted to prove:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixImageBound1296
```

No Lean proof was added. The current API stack does not yet construct a
residual-local selected terminal neighbor/predecessor image with cardinality
`<= 1296`.

## Exact no-closure blocker

The next missing theorem should isolate the terminal-neighbor selection burden,
tentatively:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborImageBound1296
```

It should bridge into:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalTerminalSuffixImageBound1296
```

The missing theorem must construct, for each v2.121 bookkeeping residual fiber
and each essential parent `p`:

- a selected terminal predecessor/neighbor `q ∈ residual`;
- last-edge adjacency `p ∈ neighborFinset q` when `residual.card ≠ 1`;
- residual-local reachability or prefix evidence from canonical residual data to
  `q`;
- residual suffix evidence from `q` to `p`;
- selected terminal-neighbor image cardinality `<= 1296`.

The important missing content is the image bound for the selected terminal
neighbors. Once that selected image is supplied, the remaining terminal-suffix
structure is projection/repacking plus local walk evidence.

## Existing APIs checked

The available APIs remain insufficient:

- `plaquetteGraphPreconnectedSubsetsAnchoredCard_root_exists_induced_path`
  gives a residual path to a target. A last edge can be conceptually extracted
  from such a path, but this does not bound the image of all selected terminal
  predecessors over the residual fiber.
- `simpleGraph_walk_exists_adj_start_of_ne` and
  `simpleGraph_walk_exists_adj_start_and_tail_of_ne` expose first-edge data.
  They may support pure path splitting, but they do not prove a `<= 1296`
  selected terminal-neighbor image bound.
- `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296_tail_to_member`
  and `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParent1296_reachable`
  are first-shell/root-shell reachability tools. They do not select the
  immediate predecessor adjacent to the target.
- `plaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent`
  and its physical wrapper give deleted-vertex adjacency to a residual parent,
  but the deleted vertex lies outside the residual and cannot be terminal
  predecessor data for this route.
- Local degree, residual size, raw residual frontier growth, and the v2.124
  packing theorem do not construct the selected terminal-neighbor image bound.

## Non-confusions

This attempt does not treat path existence, root/root-shell reachability, local
degree, residual cardinality, raw frontier growth, empirical bounded search, or
packing an already bounded menu as proof of selected terminal-neighbor image
cardinality `<= 1296`.

It does not use deleted-vertex adjacency outside the residual as terminal
predecessor data and does not choose terminal predecessors post-hoc from a
current `(X, deleted X)` witness.

## Validation

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

passed for the current Lean state. No new theorem was introduced by this
attempt, so no new theorem-specific axiom trace was needed.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, or Clay-level claim moved.

## Next task

Scope the sharper terminal-neighbor image theorem:

```text
CODEX-F3-TERMINAL-NEIGHBOR-IMAGE-BOUND-SCOPE-001
```

The scope should isolate selected terminal-neighbor image cardinality `<= 1296`
from residual path splitting and from the already-defined terminal-suffix
repacking interface.
