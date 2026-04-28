# F3 residual-fiber canonical last-edge selected-image scope v2.131

Task: `CODEX-F3-RESIDUAL-FIBER-CANONICAL-LAST-EDGE-IMAGE-SCOPE-001`

## Purpose

The v2.130 attempt showed that
`PhysicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296` is still
too compressed as a proof target.  It asks directly for a residual-indexed
terminal-predecessor selector plus a selected-image bound.  The next target
should expose the missing canonical path or terminal-edge data first, then
derive the v2.129 selector by projection.

This scope is dashboard-only.  No Lean statement was added because the exact
canonical-path API should be reviewed before hardening the signature in Lean.

## Recommended Lean Target

Recommended name:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296
```

Recommended shape:

```lean
def PhysicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    -- same v2.121 bookkeeping hypotheses as v2.129:
    bookkeepingChoice deleted parentOf essential →
    bookkeepingImage essential parentOf deleted →
    bookkeepingEssentialSubset essential →
      ∃ canonicalLastEdgeData :
        ∀ residual,
          {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual} →
            PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgeData
              residual p.1,
        (∀ residual
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}),
          residual.card ≠ 1 →
            p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset
              ((canonicalLastEdgeData residual p).predecessor.1)) ∧
        (∀ residual,
          ((essential residual).attach.image
            (fun p =>
              (canonicalLastEdgeData residual p).predecessor.1)).card ≤ 1296)
```

The placeholders `bookkeepingChoice`, `bookkeepingImage`, and
`bookkeepingEssentialSubset` should be replaced with the exact hypotheses
already used by
`PhysicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296`.

The intended data type can reuse the existing structure:

```lean
PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgeData
```

That structure already packages:

- a target in the residual;
- proof that the target is the essential parent;
- a predecessor in the residual;
- an induced residual walk from predecessor to target;
- a `Fin 1296` code.

## Exact Bridge To v2.129

The bridge target should be:

```lean
physicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296_of_residualFiberCanonicalLastEdgeImageBound1296
```

Bridge construction:

1. obtain `canonicalLastEdgeData` from the new target;
2. define

```lean
terminalPredOfParent residual p :=
  (canonicalLastEdgeData residual p).predecessor
```

3. use the target equation and path field from
   `PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgeData` to supply the
   residual path clause required by v2.129;
4. pass through the last-edge adjacency clause;
5. pass through the selected predecessor image cardinality bound.

This bridge is a projection/repacking theorem.  It should not construct the
canonical path itself and should not use deleted-vertex adjacency outside the
residual.

## Why This Is Not Just v2.129 Restated

v2.129 asks for a selector:

```lean
terminalPredOfParent residual p
```

and separately asks for path and image evidence.  The new target asks for a
canonical last-edge datum whose predecessor is projected into that selector.
This isolates the next missing graph theorem: construct residual-local
canonical path/last-edge data and prove the image of the projected predecessor
is `<= 1296`.

The future proof burden therefore has two visible components:

1. canonical residual path or last-edge extraction;
2. selected predecessor image-cardinality bound.

## Non-Confusions

This is not root reachability.  Root reachability can provide a path to a target
inside a residual, but it does not by itself expose a canonical terminal edge or
bound the image of terminal predecessors.

This is not local degree.  Local degree bounds the neighbor set of one fixed
plaquette; the target bounds the image of selected terminal predecessors across
an entire residual fiber.

This is not a raw residual frontier bound and not a residual-size bound.  The
residual may be large and its raw frontier may grow; only the projected
canonical last-edge predecessor image is bounded.

This is not deleted-vertex adjacency.  `deleted X` is outside
`X.erase (deleted X)`, so it cannot be used as the residual terminal
predecessor.

This is not empirical evidence.  Bounded searches can motivate the target, but
they cannot prove the selected-image cardinality statement.

## Recommended Next Task

```text
CODEX-F3-RESIDUAL-FIBER-CANONICAL-LAST-EDGE-IMAGE-INTERFACE-001
```

Add the no-sorry Lean Prop/interface
`PhysicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296` and, if it
builds without sorry, prove the projection bridge
`physicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296_of_residualFiberCanonicalLastEdgeImageBound1296`.

## Validation

Dashboard note exists.  No Lean file was edited, so no `lake build` was
required for this scope.

## Non-Claims

This task does not prove:

- `PhysicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296`;
- `PhysicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296`;
- `PhysicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296`;
- any decoder theorem or compression to older constants.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No ledger status, project percentage,
README metric, planner metric, or Clay-level claim moved.
