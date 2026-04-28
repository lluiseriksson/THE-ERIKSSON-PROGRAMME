# F3 terminal-neighbor ambient value code scope v2.172

Task: `CODEX-F3-TERMINAL-NEIGHBOR-AMBIENT-VALUE-CODE-SCOPE-001`

Status: `DONE_SCOPE_DELIVERED_NO_LEAN_NO_STATUS_MOVE`

## Proposed Lean target

Tentative source theorem/interface:

- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296`

Exact bridge into the current chain:

- `physicalPlaquetteGraphResidualFiberTerminalNeighborAbsoluteSelectedValueCode1296_of_residualFiberTerminalNeighborAmbientValueCode1296`

Bridge target:

- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAbsoluteSelectedValueCode1296`

## Intended source contract

The ambient theorem should be strictly upstream of the selected-image
cardinality chain.  For each v2.121 bookkeeping residual fiber, it should
construct:

- a residual-local `terminalNeighborOfParent` selector for essential parents;
- `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` for every
  selected parent;
- an ambient absolute value code
  `{q : ConcretePlaquette physicalClayDimension L // q ∈ residual} → Fin 1296`
  or an equivalent base-zone/bookkeeping-tag domain;
- an injectivity/separation theorem showing that equal ambient codes on
  selected terminal-neighbor values force equality of those selected residual
  plaquettes.

The key difference from v2.170 is the origin of the code.  v2.170 only states
the absolute selected-value contract.  This scope requires the code to come
from an ambient structural enumeration supplied by v2.121 bookkeeping/base-zone
data, not from a selected-image bound.

## Preferred non-circular shape

The cleanest Lean-stable interface should expose an ambient code and its
selected-value separation directly:

```lean
def PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    -- same v2.121 choice/bookkeeping hypotheses as the v2.170 absolute code
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
      ∃ ambientValueCode :
        ∀ residual,
          {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} →
            Fin 1296,
        (∀ residual,
          -- ambient/base-zone/bookkeeping origin witness, to be refined in
          -- the interface task; this cannot mention selected-image card bounds
          True) ∧
        ∀ residual
          (p q : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}),
          ambientValueCode residual (terminalNeighborOfParent residual p) =
            ambientValueCode residual (terminalNeighborOfParent residual q) →
            (terminalNeighborOfParent residual p).1 =
              (terminalNeighborOfParent residual q).1
```

The placeholder origin witness should be refined by the interface task into one
of the structural routes below rather than left as `True`.

## Candidate ambient origins

1. Base-zone enumeration:
   prove selected terminal-neighbor values live in a fixed 1296-coded ambient
   base zone, then use the base-zone index as the absolute code.

2. v2.121 bookkeeping tag:
   expose a bookkeeping tag for each residual vertex and prove the tag injects
   into `Fin 1296` on selected terminal-neighbor values.

3. Canonical-last-edge/frontier coordinate:
   prove an upstream coordinate pair determines the selected value and injects
   into `Fin 1296`, without invoking selector-image compression.

The first interface attempt should prefer either base-zone enumeration or
bookkeeping tags, because both are conceptually upstream of the terminal-neighbor
selector-image cycle.  The coordinate route is more ambitious and should be
used only if the first two cannot be stated without hidden downstream
dependencies.

## Bridge shape

The bridge into v2.170 should be a direct projection:

```lean
theorem
  physicalPlaquetteGraphResidualFiberTerminalNeighborAbsoluteSelectedValueCode1296_of_residualFiberTerminalNeighborAmbientValueCode1296
    (hambient :
      PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296) :
    PhysicalPlaquetteGraphResidualFiberTerminalNeighborAbsoluteSelectedValueCode1296 := by
  -- unpack the ambient selector, selector evidence, ambient code, and
  -- selected-value separation, then repack them as the v2.170 absolute code.
```

This bridge must not build a code by first bounding the selected image.  The
menu selected for v2.170 is simply the ambient code evaluated on selected
terminal-neighbor residual values.

## Distinguishes from rejected routes

This scope is not:

- a local displacement code relative to each parent;
- equality of the per-parent `terminalNeighborCode` field;
- a selected-image packing/projection argument;
- `finsetCodeOfCardLe` on an already bounded selected image;
- empirical or bounded-search evidence;
- the v2.161 cycle
  `SelectorImageBound → SelectorCodeSeparation → CodeSeparation →
   DominatingMenu → ImageCompression → SelectorImageBound`;
- a proof from local degree, residual paths, root-shell reachability, residual
  size, raw frontier size, or deleted-vertex adjacency;
- a post-hoc choice of terminal neighbors from the current `(X, deleted X)`
  witness.

## Validation

Dashboard-only scope.  No Lean file was edited and no lake build is required
for this task.

F3-COUNT remains `CONDITIONAL_BRIDGE`; no percentage, ledger status, README
metric, planner metric, or Clay-level claim moved.

## Next Codex task

`CODEX-F3-TERMINAL-NEIGHBOR-AMBIENT-VALUE-CODE-INTERFACE-001`

Add a no-sorry Lean Prop/interface for
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296` and,
only if it builds without sorry, prove the projection bridge into
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborAbsoluteSelectedValueCode1296`.
