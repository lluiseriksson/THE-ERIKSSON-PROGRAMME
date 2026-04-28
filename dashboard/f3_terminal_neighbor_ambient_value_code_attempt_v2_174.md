# F3 terminal-neighbor ambient value code proof attempt v2.174

Task: `CODEX-F3-PROVE-TERMINAL-NEIGHBOR-AMBIENT-VALUE-CODE-001`

Status: `DONE_NO_CLOSURE_AMBIENT_BOOKKEEPING_VALUE_CODE_MISSING`

## Lean target attempted

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296
```

No Lean theorem was added.

## Exact no-closure blocker

The missing upstream theorem is an ambient/base-zone/bookkeeping absolute value
code for the v2.121 residual fibers:

```lean
{q : ConcretePlaquette physicalClayDimension L // q ∈ residual} → Fin 1296
```

with a proof that equality of this code on selected terminal-neighbor values
forces equality of those selected residual plaquettes across essential parents.

The existing v2.121 theorem

```lean
physicalPlaquetteGraph_baseAwareTerminalPredecessorBookkeeping1296
```

only supplies the total `deleted`, `parentOf`, and `essential` bookkeeping
functions plus the image/subset clauses.  It does not expose:

- a base-zone enumeration map on residual vertices;
- a bookkeeping tag map into `Fin 1296`;
- an injectivity theorem for that tag/map on residual selected
  terminal-neighbor values;
- a residual-local construction of `terminalNeighborOfParent` and
  `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` from such an
  ambient code.

Therefore the proof cannot be closed without adding a new upstream structural
principle, tentatively:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCode1296
```

whose intended bridge supplies
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296`.

## Rejected routes

The attempt did not use `finsetCodeOfCardLe` on an already bounded selected
image and did not route through the v2.161 cycle:

```text
SelectorImageBound -> SelectorCodeSeparation -> CodeSeparation ->
DominatingMenu -> ImageCompression -> SelectorImageBound
```

It also did not treat any of the following as proof of absolute selected-value
separation:

- local displacement codes;
- parent-relative `terminalNeighborCode` equality;
- residual size;
- raw frontier size;
- residual paths;
- root-shell reachability;
- deleted-vertex adjacency;
- empirical search;
- post-hoc terminal-neighbor choices from a current witness.

## Validation

`lake build YangMills.ClayCore.LatticeAnimalCount` passed.

No new theorem was introduced, so no new theorem-specific `#print axioms` trace
is required for this attempt.  The previously landed v2.173 bridge remains at
the canonical trace `[propext, Classical.choice, Quot.sound]`.

F3-COUNT remains `CONDITIONAL_BRIDGE`; no percentage, status, README metric,
planner metric, ledger row, or Clay-level claim moved.

## Next Codex task

`CODEX-F3-TERMINAL-NEIGHBOR-AMBIENT-BOOKKEEPING-TAG-CODE-SCOPE-001`

Scope the upstream ambient bookkeeping-tag/base-zone code theorem and its bridge
into `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientValueCode1296`.
