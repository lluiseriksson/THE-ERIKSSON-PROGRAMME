# F3 residual-fiber canonical last-edge image bound attempt v2.134

Task: `CODEX-F3-PROVE-RESIDUAL-FIBER-CANONICAL-LAST-EDGE-IMAGE-BOUND-001`

Target:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296
```

## Result

No Lean proof was added. The theorem does not close from the current
residual-fiber APIs without an additional residual-local terminal-edge selector
and selected-image cardinality theorem.

The v2.133 projection bridge is available:

```lean
physicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296_of_residualFiberCanonicalLastEdgeImageBound1296
```

but the producer theorem itself still lacks the data required by the v2.132
interface.

## Exact blocker

The missing ingredient is a residual-local construction that, for every
v2.121 bookkeeping residual fiber and essential parent, supplies canonical
last-edge data:

- a residual-local path or canonical path certificate ending at the essential
  parent;
- the immediate predecessor on the terminal edge of that path;
- proof that this predecessor lies in the residual and is adjacent to the
  essential parent;
- proof that the selected predecessor image over the whole residual fiber has
  cardinality `<= 1296`.

Existing APIs do not currently provide this package.

## Why existing APIs are insufficient

`physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_rootShellParent1296` and
its reachability companion provide a bounded first-shell/root-shell parent and
a path from that parent toward a target in the residual. They do not extract the
terminal predecessor adjacent to the target parent, and the first-shell image
bound is not the selected terminal-predecessor image bound required here.

Root reachability and induced-path existence show that residual vertices are
reachable from the root inside an anchored bucket. They do not provide a
residual-local canonical last-edge selector with image cardinality `<= 1296`.

The local neighbor bound `neighborFinset.card <= 1296` controls the neighbors
of one fixed plaquette. It does not bound the image of selected terminal
predecessors across a residual fiber.

The deleted vertex from the current safe-deletion witness is outside the
residual `X.erase (deleted X)`, so its adjacency to `parentOf X` cannot be used
as terminal-predecessor data.

Bounded search evidence remains empirical and was not used as proof.

## Validation

`lake build YangMills.ClayCore.LatticeAnimalCount` passed before this note was
recorded. No new theorem was introduced, so there is no new theorem-specific
axiom trace.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No ledger status, project percentage,
README metric, planner metric, or Clay-level claim moved.

## Next task

Create a scope task for a sharper residual-fiber terminal-edge selector, e.g.
`PhysicalPlaquetteGraphResidualFiberCanonicalTerminalEdgeSelector1296`, whose
bridge feeds `PhysicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296`.
The scope must distinguish terminal-edge selected-image cardinality from
root-shell reachability, local degree, residual size, raw residual frontier, and
deleted-vertex adjacency outside the residual.
