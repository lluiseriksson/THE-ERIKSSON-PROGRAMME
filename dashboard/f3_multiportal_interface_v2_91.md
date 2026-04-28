# F3 Multi-Portal Interface v2.91

Timestamp: 2026-04-27T11:00:00Z

Task: `CODEX-F3-MULTIPORTAL-INTERFACE-001`

## Outcome

Lean interface added:

```lean
PhysicalPlaquetteGraphMultiPortalSupportedSafeDeletionOrientation1296x1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean:2994
```

The interface is residual-only but not root-only.  It supplies:

- a canonical deleted plaquette choice;
- a canonical parent choice;
- the essential chosen-parent image over each residual fiber;
- a residual-only portal menu of cardinality at most `1296`;
- a residual-indexed `portalOfParent` map proving each essential parent lies in
  the local neighbor shell of one portal from that residual menu.

It does not reintroduce the blocked root-only portal policy.

## Why No Bridge Was Added

The attempted bridge to the existing product decoder contract is blocked by an
arity mismatch.

The existing target:

```lean
PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296
```

has a symbol:

```lean
Fin 1296 × Fin 1296
```

For a multi-portal route, the honest reconstruction data has three finite
choices:

```text
portal-code       : choose a residual portal from portalMenu residual
parent-code       : choose parent inside the portal-local neighbor shell
deleted-code      : choose deleted plaquette inside the parent-local neighbor shell
```

So the direct, no-compression shape is:

```text
Fin 1296 × Fin 1296 × Fin 1296
```

or equivalently:

```lean
Fin 1296 × (Fin 1296 × Fin 1296)
```

Adding a bridge to the existing two-component decoder would require either:

- a compression theorem from the two parent-selection components into one
  `Fin 1296`, which is not currently proved and would need Cowork constants
  audit; or
- an existential/post-hoc deleted-vertex decoder, which is forbidden.

Therefore no bridge theorem was added in this task.

## Relation To v2.90 Scope

The Lean interface implements the v2.90 shape as an honest proposition.  It
keeps the distinction between:

- product-symbol progress for the strengthened route; and
- the old single `Fin 1296` decoder constant, which remains unclaimed.

## Recommended Next Task

```text
CODEX-F3-TRIPLESYMBOL-DECODER-INTERFACE-001
```

Objective: add a separate triple-symbol decoder contract, for example:

```lean
PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296
```

and, if safe, a no-sorry bridge:

```lean
PhysicalPlaquetteGraphMultiPortalSupportedSafeDeletionOrientation1296x1296
  -> PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296x1296
```

This should remain clearly separated from the old `1296` and `1296 x 1296`
constants unless a compression theorem is later proved and audited.

## Validation

Command:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result:

```text
Build completed successfully (8184 jobs).
```

No theorem proof was added.  No `sorry`; no new project axiom.

## Honesty Status

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  No ledger row, project percentage,
README metric, planner metric, or Clay-level claim moves from this interface
task.
