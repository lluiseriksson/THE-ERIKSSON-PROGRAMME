# F3 residual terminal-neighbor selector image bound attempt (v2.149)

Task: `CODEX-F3-PROVE-TERMINAL-NEIGHBOR-SELECTOR-IMAGE-BOUND-001`

## Result

Attempted to prove:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296
```

No Lean proof was added. The current API stack still does not construct a
residual-indexed terminal-neighbor selector whose selected image has
cardinality `<= 1296` over every v2.121 bookkeeping residual fiber.

## Exact No-Closure Blocker

The missing ingredient is a residual-fiber terminal-neighbor image compression
or domination theorem, tentatively:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborImageCompression1296
```

It must construct, for each bookkeeping residual fiber and essential parent set,
a residual-local selector

```lean
terminalNeighborOfParent :
  ∀ p ∈ essential residual, {q // q ∈ residual}
```

with:

* last-edge adjacency from the selected `q` to the target parent in the
  non-singleton residual branch;
* residual-local walk/prefix/suffix evidence tying the selected `q` to the
  target parent;
* selected image cardinality
  `((essential residual).attach.image (fun p => (terminalNeighborOfParent residual p).1)).card ≤ 1296`.

The blocker is specifically the selected-image bound. Local existence of a
neighbor for each parent is not enough: choosing a neighbor independently can
produce an image as large as the residual or essential frontier. The proof needs
a structural compression/dominating-image lemma, not merely path existence.

## Existing APIs Checked

The available APIs remain insufficient:

* residual path existence
  `plaquetteGraphPreconnectedSubsetsAnchoredCard_root_exists_induced_path`
  gives connectivity, not a bounded selected terminal-neighbor image;
* `simpleGraph_walk_exists_adj_start_of_ne` and
  `simpleGraph_walk_exists_adj_start_and_tail_of_ne` split a first edge, not a
  terminal-neighbor selector image;
* root/root-shell APIs and `rootShellCode1296` bound first-shell data from the
  root, not terminal-neighbor images adjacent to arbitrary essential parents;
* `plaquetteGraph_neighborFinset_card_le_physical_ternary` bounds one fixed
  plaquette's local degree, not the image of a selector over a residual fiber;
* deleted-vertex adjacency supplies a neighbor outside the residual and is not
  terminal-neighbor data;
* v2.124 packing can code an already bounded explicit menu, but does not
  construct the menu or prove its selected-image cardinality.

## Non-Confusions

This attempt does not treat residual path existence/splitting,
root/root-shell reachability, local degree, residual size, raw frontier growth,
deleted-vertex adjacency, empirical search, or packing an already bounded menu
as proof of selected-image cardinality `<= 1296`.

It does not choose terminal neighbors post-hoc from a current `(X, deleted X)`
witness and does not use deleted-vertex adjacency outside the residual as
terminal-predecessor data.

## Validation

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

passed for the current Lean state. No new theorem was introduced by this
attempt, so no new theorem-specific axiom trace was needed.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, or Clay-level claim moved.

## Next Task

Scope the compression/dominating-image theorem:

```text
CODEX-F3-TERMINAL-NEIGHBOR-IMAGE-COMPRESSION-SCOPE-001
```

