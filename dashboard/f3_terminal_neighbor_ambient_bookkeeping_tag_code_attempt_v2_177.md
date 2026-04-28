# F3 terminal-neighbor ambient bookkeeping-tag code proof attempt v2.177

Task: `CODEX-F3-PROVE-TERMINAL-NEIGHBOR-AMBIENT-BOOKKEEPING-TAG-CODE-001`

Status: `DONE_NO_CLOSURE_RESIDUAL_BOOKKEEPING_TAG_MAP_MISSING`

## Lean target attempted

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCode1296
```

No Lean theorem was added.

## Exact no-closure blocker

The current Lean environment has an interface for a bookkeeping-tag code, but
does not yet contain the structural source needed to prove it:

```lean
∀ residual,
  {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} → Fin 1296
```

together with a selected-value separation theorem for the values selected by
`terminalNeighborOfParent`.

The proved v2.121 theorem

```lean
physicalPlaquetteGraph_baseAwareTerminalPredecessorBookkeeping1296
```

only constructs the total bookkeeping functions `deleted`, `parentOf`, and
`essential`, plus the residual-fiber image and subset clauses.  It does not
construct any residual vertex tag map, does not identify a base-zone/tag domain
for residual vertices, and does not prove tag injectivity on residual values or
on selected terminal-neighbor values.

The next upstream theorem should isolate exactly that missing structural
ingredient, tentatively:

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingTagMap1296
```

with an intended bridge into:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCode1296
```

## Why the proof cannot be closed from existing interfaces

Existing terminal-neighbor interfaces can provide selector-shaped data only as
assumptions of later contracts.  The only generic way visible in Lean to obtain
an injective `Fin 1296` code is `finsetCodeOfCardLe`, but applying it here to
the selected terminal-neighbor image would use selected-image cardinality as the
source of the code.  That is exactly the circular route rejected by this task.

Likewise, the per-witness `terminalNeighborCode` field in
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` is
parent-relative selector evidence, not an ambient residual-value bookkeeping
tag.  Equality of those local codes is not a proof of equality of selected
terminal-neighbor values across different essential parents.

## Rejected routes

This attempt did not use:

- selected-image cardinality;
- `finsetCodeOfCardLe` on an already bounded selected image;
- the v2.161 cycle
  `SelectorImageBound → SelectorCodeSeparation → CodeSeparation →
   DominatingMenu → ImageCompression → SelectorImageBound`;
- local displacement codes;
- parent-relative `terminalNeighborCode` equality;
- residual size, raw frontier size, residual paths, root-shell reachability,
  local degree, deleted-vertex adjacency, or empirical search;
- post-hoc terminal-neighbor choices from a current witness.

## Validation

`lake build YangMills.ClayCore.LatticeAnimalCount` passed.

No new theorem was introduced in this attempt, so no new theorem-specific
`#print axioms` trace is required.  The v2.176 bridge remains at
`[propext, Classical.choice, Quot.sound]`.

F3-COUNT remains `CONDITIONAL_BRIDGE`; no percentage, status, README metric,
planner metric, ledger row, or Clay-level claim moved.

## Next Codex task

`CODEX-F3-RESIDUAL-FIBER-BOOKKEEPING-TAG-MAP-SCOPE-001`

Scope the upstream residual-fiber bookkeeping tag map theorem and the bridge
into `PhysicalPlaquetteGraphResidualFiberTerminalNeighborAmbientBookkeepingTagCode1296`.
