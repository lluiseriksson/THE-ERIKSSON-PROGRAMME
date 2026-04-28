# F3 Last-Edge Dominating-Set Bound Attempt v2.112

Task: `CODEX-F3-PROVE-LAST-EDGE-DOMINATING-SET-BOUND-001`

## Result

No Lean proof was added for:

```lean
PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296
```

The v2.111 interface and bridge remain valid, but the actual producer theorem is
not derivable from the currently available Lean API without an additional
structural lemma.

## Exact No-Closure Blocker

The missing theorem is a residual-only terminal-predecessor domination result:

```text
For every residual bucket, the essential parent fiber admits a residual-only
selected terminal-predecessor menu of cardinality <= 1296, together with an
injective Fin 1296 code, such that every non-singleton essential parent is
adjacent to its selected terminal predecessor.
```

Existing Lean ingredients do not supply this.

What exists:

- safe deletion for each current bucket `X`;
- parent/deleted-neighbor witnesses attached to a current `(X, deleted X)`;
- root-shell and first-shell reachability APIs;
- local degree bounds for one fixed plaquette/portal.

What is missing:

- a residual-only selection of terminal predecessors over the whole residual
  fiber;
- a proof that the selected terminal-predecessor image has cardinality `<= 1296`;
- a separation code into `Fin 1296` for that selected image.

## Why Existing APIs Are Insufficient

The deleted-vertex residual-neighbor helpers choose parent data from the current
safe-deletion witness.  Using them here would choose a predecessor post-hoc from
`(X, deleted X)`, which is one of the stop conditions.

The root-shell APIs provide bounded first-shell reachability from the anchor.
They do not identify the immediate last-edge predecessor adjacent to each
essential parent.

The local neighbor bound

```lean
plaquetteGraph_neighborFinset_card_le_physical_ternary
```

bounds the degree of one fixed plaquette.  It does not bound the selected
terminal-predecessor image needed across an entire residual fiber.

The v2.109 bounded search found no growth beyond `2` in tested cases, but that
is empirical scaffolding only and was not used as proof.

## Validation

No Lean file was edited by this no-closure attempt.  The existing module build
was rerun:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

and passed.

## Non-Claims

This task does not prove:

- `PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`,
- `PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296`,
- `PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296`,
- compression to older `1296` or `1296x1296` constants.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No ledger row, project percentage,
README metric, planner metric, or Clay-level claim moved.

## Next Target

```text
CODEX-F3-TERMINAL-PREDECESSOR-DOMINATION-SCOPE-001
```

Scope a sharper residual-only terminal-predecessor domination theorem, separating
the graph-theoretic selected-image bound from the base-aware deletion/parent
bookkeeping in `PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`.
