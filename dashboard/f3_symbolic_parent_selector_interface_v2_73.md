# F3 Symbolic Parent Selector Interface v2.73

Timestamp: 2026-04-27T04:45:00Z

Task: `CODEX-F3-SYMBOLIC-PARENT-SELECTOR-INTERFACE-001`

## What Landed

Codex added a parallel strengthened B.2 decoder route in
`YangMills/ClayCore/LatticeAnimalCount.lean`.

New Lean identifiers:

```lean
PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296
PhysicalPlaquetteGraphSymbolicResidualParentSelector1296
physicalPlaquetteGraphDeletedVertexDecoderStep1296x1296_of_symbolicResidualParentSelector1296
```

The new contract uses a product symbol:

```lean
Fin 1296 × Fin 1296
```

The first component selects a residual parent/frontier branch.  The second
component is the existing local neighbor code consumed by:

```lean
physicalNeighborDecodeOfStepCode
physicalNeighborDecodeOfStepCode_spec
```

## What This Does Not Claim

This does not prove the old `PhysicalPlaquetteGraphDeletedVertexDecoderStep1296`
contract.  It does not preserve the old alphabet constant.  The direct product
alphabet has size `1296^2 = 1679616`, and any downstream use must be audited
before F3-COUNT, F3-MAYER, or any small-beta constant moves.

The v2.48-v2.72 residual-only artifacts remain intact.  They are now diagnostic
evidence for why the residual-only parent selector was too strong.

## Validation

Build:

```powershell
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result:

```text
Build completed successfully (8184 jobs).
```

Pinned trace:

```text
YangMills.physicalPlaquetteGraphDeletedVertexDecoderStep1296x1296_of_symbolicResidualParentSelector1296
depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`.  No new project axiom.

## Project Status

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  No Clay, lattice, honest-discount,
named-frontier, README, or planner percentage moved.

Recommended next task: prove or precisely fail the actual symbolic selector
content:

```lean
PhysicalPlaquetteGraphSymbolicResidualParentSelector1296
```
