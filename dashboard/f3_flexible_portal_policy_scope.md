# F3 Flexible Portal Policy Scope v2.90

Timestamp: 2026-04-27T10:45:00Z

Task: `CODEX-F3-FLEXIBLE-PORTAL-POLICY-SCOPE-001`

## Outcome

Scope-only.  No Lean file was edited in this task.

The root-only portal policy from v2.88-v2.89 is blocked by the abstract path
pattern:

```text
root -- a -- b
```

The next viable route is a residual-only multi-portal policy.  A residual bucket
should provide a small menu of portal points, and each essential chosen parent
should be supported by one portal from that residual menu.  The parent is then
coded by:

```text
(portal-code, local-neighbor-code)
```

This deliberately targets a product-symbol route.  It does not claim the old
single `Fin 1296` orientation-code constant.

## Proposed Lean-Stable Target

Recommended new interface:

```lean
PhysicalPlaquetteGraphMultiPortalSupportedSafeDeletionOrientation1296x1296
```

Suggested shape:

```lean
∀ {L : Nat} [NeZero L]
  (root : ConcretePlaquette physicalClayDimension L) (k : Nat),
  ∃ deleted :
    Finset (ConcretePlaquette physicalClayDimension L) →
      ConcretePlaquette physicalClayDimension L,
  ∃ parentOf :
    Finset (ConcretePlaquette physicalClayDimension L) →
      ConcretePlaquette physicalClayDimension L,
  ∃ essential :
    Finset (ConcretePlaquette physicalClayDimension L) →
      Finset (ConcretePlaquette physicalClayDimension L),
  ∃ portalMenu :
    Finset (ConcretePlaquette physicalClayDimension L) →
      Finset (ConcretePlaquette physicalClayDimension L),
  ∃ portalOfParent :
    ∀ residual,
      {p : ConcretePlaquette physicalClayDimension L // p ∈ essential residual} →
        ConcretePlaquette physicalClayDimension L,
    -- essential image over each residual fiber, as in v2.81/v2.87
    (∀ residual,
      essential residual =
        ((plaquetteGraphPreconnectedSubsetsAnchoredCard
            physicalClayDimension L root k).filter
            (fun X => X.erase (deleted X) = residual)).image parentOf) ∧
    -- portal menu is residual-only and bounded by the first product symbol
    (∀ residual,
      portalMenu residual ⊆ residual ∧ (portalMenu residual).card ≤ 1296) ∧
    -- every essential parent is supported by a residual-only portal
    (∀ residual p,
      portalOfParent residual p ∈ portalMenu residual ∧
      p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset
        (portalOfParent residual p)) ∧
    -- safe-deletion and local deleted-vertex support
    ∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
      (hk : 2 ≤ k)
      (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
        physicalClayDimension L root k),
      deleted X ∈ X ∧
      deleted X ≠ root ∧
      X.erase (deleted X) ∈
        plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root (k - 1) ∧
      parentOf X ∈ X.erase (deleted X) ∧
      parentOf X ∈ essential (X.erase (deleted X)) ∧
      deleted X ∈
        (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)
```

This is Lean-stable as an interface, but it is not yet added to Lean here
because the task is a scope task and the bridge target below should be reviewed
before growing another interface block.

## How It Avoids The v2.89 Blocker

In the path pattern:

```text
root -- a -- b
```

For `X = {root, a, b}`, the safe deletion is `b`, and the residual is
`{root, a}`.  The parent of `b` can be `a`.

The root-only policy failed because it forced:

```text
parentOf X = root
```

The multi-portal policy instead allows the residual-local parent `a`, supported
by the residual-local portal `root`:

```text
portalMenu {root, a} = {root}
parentOf X = a
portalOfParent {root, a} a = root
```

For longer path-like residuals, the portal menu can move along the residual
rather than forcing every chosen parent to be adjacent to the anchored root.
This is the essential difference: the support is residual-only, but not
root-only.

## Bridge Target

Primary bridge target:

```lean
PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296
```

Recommended intermediate bridge:

```lean
PhysicalPlaquetteGraphMultiPortalSupportedSafeDeletionOrientation1296x1296
  -> PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296
```

or, if the existing bridge chain should be preserved explicitly:

```lean
PhysicalPlaquetteGraphMultiPortalSupportedSafeDeletionOrientation1296x1296
  -> PhysicalPlaquetteGraphSafeDeletionOrientationCodeBound1296x1296
  -> PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296
```

It should not be bridged to:

```lean
PhysicalPlaquetteGraphPortalSupportedSafeDeletionOrientation1296
```

unless a single residual portal covering all essential parents is later proved.
It should also not be bridged to the old single `Fin 1296` code without a
separate compression theorem and Cowork constants audit.

## Next Lean Task

```text
CODEX-F3-MULTIPORTAL-INTERFACE-001
```

Add the `1296 x 1296` multi-portal interface and the no-sorry bridge to the
existing product-symbol deleted-vertex decoder contract, if the bridge can be
written without claiming compression back to `Fin 1296`.

## Honesty Status

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  No ledger row, project percentage,
README metric, planner metric, or Clay-level claim moves from this scope task.
