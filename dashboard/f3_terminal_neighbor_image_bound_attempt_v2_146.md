# F3 residual canonical terminal-neighbor image bound attempt (v2.146)

Task: `CODEX-F3-PROVE-TERMINAL-NEIGHBOR-IMAGE-BOUND-001`

## Result

Attempted to prove:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalTerminalNeighborImageBound1296
```

No Lean proof was added. The current API stack still does not construct a
residual-local selected terminal-neighbor image with cardinality `<= 1296` over
the v2.121 bookkeeping residual fibers.

## Exact no-closure blocker

The missing theorem is a residual-local terminal-neighbor selector with a
selected-image bound, tentatively:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296
```

It should supply, for each v2.121 bookkeeping residual fiber and each essential
parent `p`:

- a selected `q ∈ residual`;
- last-edge adjacency `p ∈ neighborFinset q` when `residual.card ≠ 1`;
- residual-local prefix/suffix or walk evidence connecting the canonical source,
  `q`, and `p`;
- a selected-image cardinality bound
  `((essential residual).attach.image (fun p => q_of residual p)).card ≤ 1296`.

This has to be a bound on the selected terminal-neighbor image over the fiber,
not a bound on one fixed local neighborhood and not a cardinality bound for the
whole residual/frontier.

## Existing APIs checked

The available APIs are insufficient:

- `plaquetteGraphPreconnectedSubsetsAnchoredCard_root_exists_induced_path`
  gives residual path existence, but it does not choose a terminal neighbor with
  a globally bounded selected image over the residual fiber.
- `simpleGraph_walk_exists_adj_start_of_ne` and
  `simpleGraph_walk_exists_adj_start_and_tail_of_ne` split the first edge of a
  walk. They do not provide terminal-edge extraction with a selected-image
  cardinality bound.
- `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_exists_rootShellCode1296_tail_to_member`,
  `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParent1296_reachable`,
  and related root-shell APIs name first-shell/root-neighbor data. They do not
  select the immediate predecessor adjacent to each target parent.
- `plaquetteGraph_neighborFinset_card_le_physical_ternary` and
  `physicalPlaquetteGraphBranchingBound1296` bound the local degree of one fixed
  plaquette. They do not bound the image of selected terminal neighbors across a
  residual fiber.
- `plaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent`
  and the physical wrapper give adjacency between a deleted vertex and a
  residual parent. The deleted vertex lies outside the residual, so it cannot be
  used as terminal-predecessor data here.
- v2.124 packing encodes an already bounded explicit menu. It does not construct
  the selected terminal-neighbor menu or prove its cardinality bound.

## Non-confusions

This attempt does not treat residual path existence/splitting,
root/root-shell reachability, local degree, residual cardinality, raw frontier
growth, empirical bounded search, or packing an already bounded menu as proof of
selected terminal-neighbor image cardinality `<= 1296`.

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

Scope the sharper selector/image theorem:

```text
CODEX-F3-TERMINAL-NEIGHBOR-SELECTOR-IMAGE-SCOPE-001
```

The scope should isolate residual-local terminal-neighbor selection and the
selected-image cardinality proof from path existence, local degree, residual
size, raw frontier, root-shell reachability, deleted-vertex adjacency, and
packing.
