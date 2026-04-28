# F3 residual-fiber terminal-predecessor image bound interface v2.129

Task: `CODEX-F3-RESIDUAL-FIBER-TERMINAL-PREDECESSOR-IMAGE-BOUND-INTERFACE-001`

## Result

Added the no-sorry Lean interface:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296
```

and the no-sorry bridge:

```lean
physicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296_of_residualFiberTerminalPredecessorImageBound1296
```

The interface is intentionally narrower than
`PhysicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296`.  It
does not directly existentially package a terminal-predecessor menu.  Instead,
for the same v2.121 bookkeeping inputs, it asks for a residual-indexed
`terminalPredOfParent` selector, last-edge adjacency, residual path evidence,
and the selected-image bound:

```lean
((essential residual).attach.image
  (fun p => (terminalPredOfParent residual p).1)).card <= 1296
```

The bridge then defines `terminalPredMenu residual` to be exactly that selected
image and repacks the membership, identity, adjacency, path, and card clauses
into `PhysicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296`.

## Lean Locations

- Interface: `YangMills/ClayCore/LatticeAnimalCount.lean:3418`
- Bridge theorem: `YangMills/ClayCore/LatticeAnimalCount.lean:3549`
- Axiom trace: `YangMills/ClayCore/LatticeAnimalCount.lean:6124`

## Validation

`lake build YangMills.ClayCore.LatticeAnimalCount` passed.

The bridge theorem axiom trace is:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, new project axiom, empirical search evidence, or post-hoc
deleted-vertex/terminal-predecessor choice was introduced.

## Non-Claims

This does not prove
`PhysicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296`.

This does not prove the old `Fin 1296`, product `Fin 1296 x Fin 1296`, or
triple-symbol decoder chain unconditionally.

This does not treat deleted-vertex adjacency outside the residual as
terminal-predecessor data.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric,
planner metric, or Clay-level claim moved.

## Recommended Next Task

```text
CODEX-F3-PROVE-RESIDUAL-FIBER-TERMINAL-PREDECESSOR-IMAGE-BOUND-001
```

Attempt the actual proof of
`PhysicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296`, or
reduce it to the next exact no-closure blocker.
