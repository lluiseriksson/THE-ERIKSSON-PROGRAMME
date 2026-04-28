# F3 Essential Frontier Bridge Interface v2.81

Timestamp: 2026-04-27T08:00:00Z

Task: `CODEX-F3-ESSENTIAL-FRONTIER-BRIDGE-INTERFACE-001`

## Lean Interface Added

Codex added the structured proposition:

```lean
PhysicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:2891
```

The proposition supplies, for each physical `root` and `k`:

- `deleted`, a canonical deleted plaquette choice for each current anchored bucket,
- `parentOf`, a canonical residual parent choice for each current anchored bucket,
- `essential`, a residual-indexed finite parent menu.

The key structural clause is:

```lean
essential residual =
  ((plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k).filter
      (fun X => X.erase (deleted X) = residual)).image parentOf
```

So the bounded set is the image of chosen parents over the residual fiber of
canonical deletions, not the whole raw one-step frontier.

## Bridge Added

Codex proved:

```lean
physicalPlaquetteGraphResidualParentMenuBound1296_of_essentialSafeDeletionParentFrontierBound1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:2955
```

Type:

```lean
PhysicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296
  -> PhysicalPlaquetteGraphResidualParentMenuBound1296
```

The proof simply takes the residual menu to be `essential` and projects the
canonical `deleted` and `parentOf` witnesses.

## Bridge Chain

The current strengthened-product route is:

```text
PhysicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296
  -> PhysicalPlaquetteGraphResidualParentMenuBound1296
  -> PhysicalPlaquetteGraphResidualParentMenuCovers1296
  -> PhysicalPlaquetteGraphSymbolicResidualParentSelector1296
  -> PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296
```

This is still a conditional interface chain. The essential frontier bound itself
is not proved.

## Validation

Command:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result:

```text
Build completed successfully (8184 jobs).
```

Pinned trace:

```text
YangMills.physicalPlaquetteGraphResidualParentMenuBound1296_of_essentialSafeDeletionParentFrontierBound1296
depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`. No new project axiom.

## Honesty Status

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.

The original `Fin 1296` decoder contract is not claimed. The product alphabet
route remains a strengthened route and remains constants-audit gated.

No Clay-level percentage, lattice-level percentage, honest-discount percentage,
named-frontier percentage, README metric, planner metric, or ledger status moves
from this interface task.
