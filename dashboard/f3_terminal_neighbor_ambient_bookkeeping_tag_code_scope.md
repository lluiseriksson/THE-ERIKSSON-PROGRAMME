# F3 terminal-neighbor ambient bookkeeping-tag code scope v2.175

Task: `CODEX-F3-TERMINAL-NEIGHBOR-AMBIENT-BOOKKEEPING-TAG-CODE-SCOPE-001`

Status: `DONE_SCOPE_DELIVERED_NO_LEAN_NO_STATUS_MOVE`

## Proposed Lean target

Tentative upstream theorem/interface:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCode1296
```

Exact bridge into the current chain:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296_of_residualFiberTerminalNeighborAmbientBookkeepingTagCode1296
```

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296
```

## Intended source contract

The theorem should refine the v2.173 ambient interface by making the source of
the residual value code explicit.  For each v2.121 bookkeeping residual fiber,
it should construct:

- a residual-local `terminalNeighborOfParent` selector on essential parents;
- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` for each
  selected parent;
- an ambient bookkeeping/base-zone tag code
  `{q : ConcretePlaquette physicalClayDimension L // q ∈ residual} → Fin 1296`;
- a proof that equality of this tag code on selected terminal-neighbor values
  forces equality of the selected residual plaquettes.

The code must be defined on residual values before it is evaluated on selected
terminal-neighbor values.  It is not a code on the selected-image finset and is
not derived from the selected-image cardinality bound.

## Lean-stable shape

A no-sorry interface can use the same v2.121 hypotheses as
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296`, but
with the code source narrowed to the bookkeeping-tag origin:

```lean
def PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCode1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    -- same v2.121 choice / image / subset hypotheses
    ... →
      ∃ terminalNeighborOfParent :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
      ∃ terminalNeighborSelectorEvidence :
        ∀ residual,
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}) →
            PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
              residual p.1 (terminalNeighborOfParent residual p),
      ∃ bookkeepingTagCode :
        ∀ residual,
          {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} →
            Fin 1296,
        ∀ residual
          (p q : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}),
          bookkeepingTagCode residual (terminalNeighborOfParent residual p) =
            bookkeepingTagCode residual (terminalNeighborOfParent residual q) →
            (terminalNeighborOfParent residual p).1 =
              (terminalNeighborOfParent residual q).1
```

The interface task may package `bookkeepingTagCode` in a dedicated structure if
that makes the origin auditable, but the bridge into v2.173 should set:

```lean
ambientOrigin := PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientCodeOrigin.bookkeepingTag
ambientValueCode := bookkeepingTagCode residual
```

## Bridge shape

The bridge should be projection-only:

```lean
theorem
  physicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296_of_residualFiberTerminalNeighborAmbientBookkeepingTagCode1296
    (h :
      PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCode1296) :
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296 := by
  -- unpack selector, selector evidence, bookkeepingTagCode, and separation;
  -- repack into PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCodeData
  -- with ambientOrigin = bookkeepingTag.
```

It must not construct a code from selected-image cardinality, and it must not
route through selector-image compression, code separation, dominating menus, or
image bounds.

## Actual mathematical burden

The later proof of this theorem must supply two independent pieces:

1. **A residual-value tag map.**  v2.121 currently provides total
   `deleted`/`parentOf`/`essential` bookkeeping and image/subset clauses only.
   It does not yet expose a tag map from residual values into `Fin 1296`.

2. **Selected-value separation.**  The theorem must prove that equal tag codes
   on the values picked by `terminalNeighborOfParent` force equality of those
   selected residual plaquettes.  This is stronger than saying each selected
   parent has a local `terminalNeighborCode`.

Candidate upstream sources remain:

- base-zone enumeration, if residual selected terminal-neighbor values can be
  shown to live in a fixed 1296-coded ambient zone;
- a v2.121 bookkeeping tag, if the totalization can be strengthened to assign
  injective tags to residual values;
- canonical-last-edge/frontier coordinates, only if the coordinate pair
  determines the selected value without using downstream image compression.

## Distinguishes from rejected routes

This scope is not:

- selected-image cardinality;
- `finsetCodeOfCardLe` on an already bounded selected image;
- the v2.161 cycle
  `SelectorImageBound → SelectorCodeSeparation → CodeSeparation →
   DominatingMenu → ImageCompression → SelectorImageBound`;
- local displacement coding;
- parent-relative `terminalNeighborCode` equality;
- empirical or bounded-search evidence;
- a proof from residual size, raw frontier size, residual paths,
  root-shell reachability, local degree, or deleted-vertex adjacency;
- a post-hoc terminal-neighbor choice from a current `(X, deleted X)` witness.

## Validation

Dashboard-only scope.  No Lean file was edited and no lake build is required
for this task.

F3-COUNT remains `CONDITIONAL_BRIDGE`; no percentage, status, README metric,
planner metric, ledger row, or Clay-level claim moved.

## Next Codex task

`CODEX-F3-TERMINAL-NEIGHBOR-AMBIENT-BOOKKEEPING-TAG-CODE-INTERFACE-001`

Add the no-sorry Lean interface and projection bridge into
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296`, only
if the bridge builds without `sorry`.
