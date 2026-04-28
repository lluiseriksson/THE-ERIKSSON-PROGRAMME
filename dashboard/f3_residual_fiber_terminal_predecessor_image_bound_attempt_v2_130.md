# F3 residual-fiber terminal-predecessor image bound attempt v2.130

Task: `CODEX-F3-PROVE-RESIDUAL-FIBER-TERMINAL-PREDECESSOR-IMAGE-BOUND-001`

## Result

No Lean proof was added for:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296
```

The v2.129 interface and bridge remain valid.  The attempted proof reduces to
one missing structural theorem: a residual-local canonical last-edge selector
whose selected predecessor image over each v2.121 bookkeeping residual fiber is
bounded by `1296`.

## Exact no-closure blocker

The existing APIs provide these relevant ingredients:

- v2.121 bookkeeping data via
  `physicalPlaquetteGraph_baseAwareTerminalPredecessorBookkeeping1296`;
- current-bucket deleted-vertex adjacency via
  `physicalPlaquetteGraphPreconnectedSubsetsAnchoredCard_deletedVertex_has_residualNeighborParent`;
- induced root reachability inside an anchored bucket via
  `plaquetteGraphPreconnectedSubsetsAnchoredCard_root_exists_induced_path`;
- local degree/cardinality bounds such as
  `plaquetteGraph_neighborFinset_card_le_physical_ternary`.

None of these constructs the required residual-indexed selector:

```lean
terminalPredOfParent :
  ∀ residual,
    {p // p ∈ essential residual} → {q // q ∈ residual}
```

with all three load-bearing properties:

1. last-edge adjacency from the selected residual predecessor to each essential
   parent when `residual.card ≠ 1`;
2. induced residual path evidence from the selected predecessor to that parent;
3. selected-image cardinality
   `((essential residual).attach.image (fun p => (terminalPredOfParent residual p).1)).card <= 1296`.

The root-reachability theorem gives a path from the root to each target parent
inside a residual bucket.  However, the currently available API does not expose
a canonical terminal edge of that path, nor prove that the collection of such
terminal predecessors over the whole residual fiber has image cardinality
`<= 1296`.

## Rejected shortcuts

Using `deleted X` as a terminal predecessor is invalid: `deleted X` is outside
the residual `X.erase (deleted X)`.

Choosing a predecessor from the current `(X, deleted X)` witness would be
post-hoc and violates the task stop condition.  The selector must be indexed by
residual data and the essential parent, not by a chosen current bucket witness.

Using the local neighbor bound of one fixed plaquette is insufficient.  The
needed bound is on the selected predecessor image across a residual fiber, not
on the neighbor set of a single portal/predecessor.

Using root-shell or first-shell reachability is insufficient.  The theorem
needs last-edge adjacency to each essential parent, plus induced residual path
evidence.

No empirical search output was used as proof.

## Next structural target

The next Lean-stable target should expose canonical path/last-edge data before
trying to prove the selected-image bound, for example:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296
```

The intended interface should take the v2.121 bookkeeping fibers and provide:

- a residual-local canonical path datum from a distinguished residual source to
  each essential parent;
- extraction of the immediate last-edge predecessor inside the residual;
- proof that this predecessor is adjacent to the essential parent in the
  non-singleton branch;
- proof that the selected predecessor image has cardinality `<= 1296`.

The bridge back to v2.129 should be:

```lean
physicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296_of_residualFiberCanonicalLastEdgeImageBound1296
```

This separates the missing path/terminal-edge structure from the already-landed
selected-image interface and avoids treating reachability, local degree, or
deleted-vertex adjacency as the bound itself.

## Validation

`lake build YangMills.ClayCore.LatticeAnimalCount` passed.

No new theorem was added, so no new theorem-specific axiom trace was introduced.
Existing relevant traces remain no larger than:

```text
[propext, Classical.choice, Quot.sound]
```

## Non-claims

This task does not prove:

- `PhysicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296`;
- `PhysicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296`;
- `PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`;
- any decoder theorem or compression to older constants.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No ledger status, project percentage,
README metric, planner metric, or Clay-level claim moved.
