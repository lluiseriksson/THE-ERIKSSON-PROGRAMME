# F3 Portal-Supported Orientation Interface v2.87

Timestamp: 2026-04-27T10:00:00Z

Task: `CODEX-F3-PORTAL-SUPPORTED-ORIENTATION-INTERFACE-001`

## Outcome

Lean interface and bridge added.

New proposition:

```lean
PhysicalPlaquetteGraphPortalSupportedSafeDeletionOrientation1296
```

New bridge theorem:

```lean
physicalPlaquetteGraphSafeDeletionOrientationCodeBound1296_of_portalSupportedSafeDeletionOrientation1296
```

The proposition is not a restatement of
`PhysicalPlaquetteGraphSafeDeletionOrientationCodeBound1296`.  It does not
provide an orientation code.  Instead, it supplies:

- a residual-only portal map;
- canonical deleted plaquette and residual parent choices;
- an essential chosen-parent image over each residual fiber;
- proof that each essential image lies in the local neighbor shell of the
  residual portal.

The bridge constructs the orientation code from
`plaquetteNeighborStepCodeBoundDim_physical_ternary`, so the `Fin 1296` code is
derived from portal-local neighbor-code injectivity rather than from any raw
residual-frontier bound.

## Bridge Chain

This adds the first bridge in the portal-supported route:

```text
PhysicalPlaquetteGraphPortalSupportedSafeDeletionOrientation1296
  -> PhysicalPlaquetteGraphSafeDeletionOrientationCodeBound1296
  -> PhysicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296
  -> PhysicalPlaquetteGraphResidualParentMenuBound1296
  -> PhysicalPlaquetteGraphResidualParentMenuCovers1296
  -> PhysicalPlaquetteGraphSymbolicResidualParentSelector1296
  -> PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296
```

The first theorem in this chain is now a no-sorry bridge.  The portal-supported
orientation theorem itself remains open.

## Validation

Command:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result:

```text
Build completed successfully (8184 jobs).
```

`#print axioms` for the new bridge reports:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry` and no new project axiom were introduced.

## Honesty Status

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  The strengthened product-symbol route
remains conditional and constants-audit gated.  No ledger row, project
percentage, README metric, or Clay-level claim moves from this interface task.

## Recommended Next Task

```text
CODEX-F3-PROVE-PORTAL-SUPPORTED-ORIENTATION-001
```

Objective: prove or precisely fail
`PhysicalPlaquetteGraphPortalSupportedSafeDeletionOrientation1296`.  The proof
must construct residual portals and portal-supported safe-deletion choices; it
must not fall back to a raw residual-frontier bound or an existential-only
`Classical.choose` decoder.
