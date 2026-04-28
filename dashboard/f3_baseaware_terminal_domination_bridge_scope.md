# F3 base-aware terminal-domination bridge scope v2.115

**Task:** `CODEX-F3-BASEAWARE-TERMINAL-DOMINATION-BRIDGE-SCOPE-001`  
**Date:** 2026-04-27  
**Status:** scope delivered; no Lean edit; no F3-COUNT status movement.

## Purpose

The v2.114 interface landed:

```lean
PhysicalPlaquetteGraphResidualTerminalPredecessorDomination1296
```

It is intentionally residual-only: it takes `(residual, essential)` and
`essential subset residual`, then supplies the terminal-predecessor menu,
injective `Fin 1296` code, residual path evidence, and non-singleton last-edge
domination.

The bridge into:

```lean
PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296
```

cannot come from that residual-only theorem alone.  The target still requires a
base-aware deletion and parent bookkeeping block over current anchored buckets
`X`.

## Exact bookkeeping theorem to isolate

Recommended new interface:

```lean
PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296
```

Intended shape:

```lean
def PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296 : Prop :=
  forall {L : Nat} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : Nat),
    exists deleted :
      Finset (ConcretePlaquette physicalClayDimension L) ->
        ConcretePlaquette physicalClayDimension L,
    exists parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) ->
        ConcretePlaquette physicalClayDimension L,
    exists essential :
      Finset (ConcretePlaquette physicalClayDimension L) ->
        Finset (ConcretePlaquette physicalClayDimension L),
      -- Current-bucket safe deletion and parent bookkeeping:
      (forall {X}
        (hk : 2 <= k)
        (hX : X in plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k),
        deleted X in X /\
        deleted X != root /\
        X.erase (deleted X) in
          plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root (k - 1) /\
        parentOf X in X.erase (deleted X) /\
        parentOf X in essential (X.erase (deleted X)) /\
        (((X.erase (deleted X)).card = 1 /\
          parentOf X = root /\
          deleted X in
            (plaquetteGraph physicalClayDimension L).neighborFinset root) \/
        ((X.erase (deleted X)).card != 1 /\
          deleted X in
            (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)))) /\
      -- Essential-parent fiber definition:
      (forall residual,
        essential residual =
          ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) /\
      -- The subset fact needed to invoke the residual-only domination theorem:
      (forall residual, essential residual subset residual)
```

This is exactly the base-aware block in
`PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`, without the
terminal predecessor menu, terminal predecessor code, or induced residual path
payload.

## Exact bridge target

The user-facing bridge target remains:

```lean
physicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296_of_terminalPredecessorDomination1296
```

The honest Lean route should likely be a two-input bridge:

```lean
physicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296_of_baseAwareBookkeeping_of_terminalPredecessorDomination1296
```

with inputs:

```lean
hbook :
  PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296

hterminal :
  PhysicalPlaquetteGraphResidualTerminalPredecessorDomination1296
```

and output:

```lean
PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296
```

The single-input name
`physicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296_of_terminalPredecessorDomination1296`
should be reserved until the base-aware bookkeeping theorem is already proved
or available as an earlier closed input.

## Bridge construction once bookkeeping exists

For fixed `(L, root, k)`:

1. Use `hbook root k` to obtain `deleted`, `parentOf`, `essential`, the
   current-bucket deletion/parent clause, the essential fiber identity, and
   `essential subset residual`.
2. For each residual, apply
   `hterminal residual (essential residual) (hessential_subset residual)`.
3. Define:
   - `terminalPredMenu residual`;
   - `terminalPredOfParent residual`;
   - `terminalPredCode residual`;
   - `terminalPredPath residual`;
   by choosing the corresponding residual-only witnesses from step 2.
4. Repack the terminal data plus the base-aware data into
   `PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`.

This bridge is a repacking lemma.  It should use no empirical search evidence
and no post-hoc predecessor choice from `(X, deleted X)`.  The terminal
predecessor selector remains a function of `(residual, essential, p)`.

## Why this is not a restatement

The proposed bookkeeping interface contains only:

- `deleted`;
- `parentOf`;
- `essential`;
- the current anchored-bucket safe-deletion/parent clause;
- the essential-fiber image identity;
- `essential residual subset residual`.

It deliberately excludes:

- `terminalPredMenu`;
- `terminalPredOfParent`;
- `terminalPredCode`;
- induced residual terminal paths;
- selected terminal-predecessor image bounds.

Those excluded clauses are exactly what
`PhysicalPlaquetteGraphResidualTerminalPredecessorDomination1296` supplies.

## Remaining proof burden

The next Lean task is to add the bookkeeping interface and, if it builds without
`sorry`, add the two-input bridge from bookkeeping plus terminal domination to
`PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`.

The actual proof of
`PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296` is still a
separate graph/deletion bookkeeping problem.  It must not choose terminal
predecessors post-hoc from `(X, deleted X)`.

## Non-claims

This scope does not prove:

- `PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296`;
- `PhysicalPlaquetteGraphResidualTerminalPredecessorDomination1296`;
- `PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`;
- any old `Fin 1296` or product-symbol decoder compression;
- F3-COUNT closure.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No ledger row, project percentage,
README metric, planner metric, or Clay-level claim moved.
