# F3 Safe-Deletion Orientation-Code Interface v2.84

Timestamp: 2026-04-27T08:45:00Z

Task: `CODEX-F3-SAFE-DELETION-ORIENTATION-CODE-INTERFACE-001`

## Result

Codex added the Lean interface:

```lean
PhysicalPlaquetteGraphSafeDeletionOrientationCodeBound1296
```

and proved the bridge:

```lean
physicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296_of_safeDeletionOrientationCodeBound1296
```

The interface is intentionally stronger than a raw menu-size assertion.  It
provides:

- canonical safe-deletion choices `deleted`,
- canonical residual parent choices `parentOf`,
- an essential chosen-parent menu `essential`,
- and an orientation code
  `orientCode residual : {p // p ∈ essential residual} -> Fin 1296`
  that is injective for every residual bucket.

The bridge derives `(essential residual).card ≤ 1296` from the injection into
`Fin 1296`.  It does not use raw residual-frontier bounds or empirical search
evidence.

## Lean Identifiers

- Prop: `PhysicalPlaquetteGraphSafeDeletionOrientationCodeBound1296`
- Bridge:
  `physicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296_of_safeDeletionOrientationCodeBound1296`
- Downstream bridge target:
  `PhysicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296`

## Validation

Command:

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result:

```text
Build completed successfully (8184 jobs).
```

Axiom trace:

```text
YangMills.physicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296_of_safeDeletionOrientationCodeBound1296
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Remaining Gap

The new open theorem is:

```lean
PhysicalPlaquetteGraphSafeDeletionOrientationCodeBound1296
```

It must still be proved by constructing safe deletions, residual parents, and
injective orientation codes over residual fibers.  This task only landed the
interface and the injection-to-cardinality bridge.

## Honesty Status

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  The strengthened product-symbol route
is still conditional and constants-audit gated.  No theorem is claimed for the
original residual-only `Fin 1296` decoder contract, and no status, percentage,
or Clay-level claim moves from this interface task.

## Recommended Next Task

```text
CODEX-F3-PROVE-SAFE-DELETION-ORIENTATION-CODE-BOUND-001
```

Objective: prove or precisely fail
`PhysicalPlaquetteGraphSafeDeletionOrientationCodeBound1296`; if it closes,
compose only through the v2.84/v2.81/v2.75/v2.73 strengthened-product bridge
chain and keep F3-COUNT gated pending Cowork constants audit.
