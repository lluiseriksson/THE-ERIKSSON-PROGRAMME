# F3 residual-fiber terminal-predecessor domination attempt v2.127

Task: `CODEX-F3-PROVE-RESIDUAL-FIBER-TERMINAL-PREDECESSOR-DOMINATION-001`

## Result

No Lean proof was added for:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296
```

The v2.126 interface and conditional bridge remain valid, but the producer is
not derivable from the currently available Lean API without an additional
residual-fiber selected-image theorem.

## Exact no-closure blocker

The v2.121 bookkeeping theorem supplies, for each current bucket `X`, a
deleted plaquette and a parent:

```lean
parentOf X ∈ X.erase (deleted X)
```

and, in the non-singleton residual branch:

```lean
deleted X ∈ (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)
```

This is not the terminal-predecessor datum required by v2.126.  The deleted
plaquette is outside the residual `X.erase (deleted X)`, while the new producer
must choose a predecessor inside the residual:

```lean
terminalPredOfParent residual p : {q // q ∈ residual}
```

with `p` adjacent to that selected predecessor whenever `residual.card ≠ 1`.

Even if induced preconnectedness can provide some residual neighbor for each
essential parent in a non-singleton residual, the missing load-bearing fact is
stronger: the image of all selected terminal predecessors over the whole
residual fiber must have cardinality `<= 1296`.  The current APIs provide local
degree bounds for one fixed plaquette and first-shell/root reachability, but
they do not bound this selected terminal-predecessor image.

## Why the tempting shortcuts are invalid

Using the deleted plaquette as the predecessor is impossible because it is not
in the residual.

Choosing the predecessor from the current witness `(X, deleted X)` would be
post-hoc across the residual fiber and violates the task stop condition.

Using the local neighbor bound

```lean
plaquetteGraph_neighborFinset_card_le_physical_ternary
```

would only bound the degree of one fixed vertex.  It does not bound the image
of a residual-indexed selected predecessor map over all essential parents.

Using root-shell reachability would produce a first-shell path witness, not the
last-edge predecessor adjacent to each essential parent.

The v2.109 bounded search found no image growth in small cases, but that
empirical evidence was not used as proof.

## Next structural target

The next Lean-stable target should isolate the exact missing selected-image
lemma, for example:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296
```

Suggested content:

For the residual fibers and essential sets produced by v2.121 bookkeeping,
construct a residual-local selected terminal-predecessor map with:

1. selected predecessor membership in the residual;
2. last-edge adjacency for every non-singleton essential parent;
3. induced residual path evidence from selected predecessor to target parent;
4. selected predecessor image cardinality `<= 1296`.

This target is sharper than the full v2.126 producer because it separates the
graph-theoretic selected-image burden from the already-proved bookkeeping and
the already-proved v2.124 packing theorem.

## Validation

No Lean file was edited by this no-closure attempt.  The existing module build
was rerun:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

and passed.

No new theorem was introduced, so no new theorem-specific axiom trace was
added.  Existing relevant theorem traces remain no larger than:

```text
[propext, Classical.choice, Quot.sound]
```

## Non-claims

This task does not prove:

- `PhysicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296`,
- `PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`
  unconditionally,
- `PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296`,
- compression to older `1296` or `1296 x 1296` constants.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No ledger status, project percentage,
README metric, planner metric, or Clay-level claim moved.
