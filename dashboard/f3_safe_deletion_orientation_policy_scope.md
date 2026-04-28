# F3 Safe-Deletion Orientation Policy Scope

Timestamp: 2026-04-27T09:15:00Z

Task: `CODEX-F3-SAFE-DELETION-ORIENTATION-POLICY-SCOPE-001`

## Purpose

The v2.85 attempt showed that the open theorem

```lean
PhysicalPlaquetteGraphSafeDeletionOrientationCodeBound1296
```

cannot be obtained from the existing safe-deletion existence theorem by
`Classical.choose`.  The missing content is a canonical orientation policy whose
chosen-parent image over each residual fiber admits an injective `Fin 1296`
code.

This note scopes a concrete policy that is narrower than the raw residual
frontier and strong enough to imply the v2.84 orientation-code theorem.

## Proposed Policy: Portal-Supported Safe Deletion

For each residual bucket `R`, choose a canonical residual portal:

```lean
physicalPlaquetteResidualPortal1296
  (root : ConcretePlaquette physicalClayDimension L)
  (R : Finset (ConcretePlaquette physicalClayDimension L)) :
  Option (ConcretePlaquette physicalClayDimension L)
```

Intended definition:

1. If `root ∈ R`, use the lexicographically first plaquette of the canonical
   root-directed spanning tree frontier of `R`.
2. Otherwise return `none`.
3. The order is the existing finite order inherited from `ConcretePlaquette`;
   if a more explicit order is needed, use the tuple
   `(site coordinates, orientation pair)` as the canonical key.

For a current anchored bucket `X`, a safe deletion `z` is **portal-supported** if
with `R = X.erase z` there are `portal` and `p` such that:

```lean
physicalPlaquetteResidualPortal1296 root R = some portal
p ∈ R
p ∈ (plaquetteGraph physicalClayDimension L).neighborFinset portal
z ∈ (plaquetteGraph physicalClayDimension L).neighborFinset p
```

The canonical policy is:

```text
deleted X  = the lexicographically least portal-supported safe deletion z
parentOf X = the lexicographically least matching parent p
```

This is not merely `Classical.choose`: the candidate set is filtered by a
residual-only portal condition, and the chosen parent is forced into a local
`1296`-bounded shell around the portal of the residual.

## Intended Fin 1296 Code

Once the portal-supported property is proved, define the essential menu exactly
as in v2.84:

```lean
essential R =
  ((plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k).filter
      (fun X => X.erase (deleted X) = R)).image parentOf
```

For `p ∈ essential R`, the portal condition proves:

```lean
p ∈ (plaquetteGraph physicalClayDimension L).neighborFinset portal
```

Use the existing local neighbor code from
`plaquetteNeighborStepCodeBoundDim_physical_ternary`:

```lean
code portal p : Fin 1296
```

as:

```lean
orientCode R ⟨p, hp⟩ = code portal p
```

Injectivity follows from the existing `Set.InjOn (code portal)` on
`neighborFinset portal`, restricted to `essential R`.

## Smallest Lean Lemma Needed

The smallest new structural lemma should be:

```lean
PhysicalPlaquetteGraphPortalSupportedSafeDeletionOrientation1296
```

Suggested shape:

```lean
def PhysicalPlaquetteGraphPortalSupportedSafeDeletionOrientation1296 : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
    ∃ portal :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Option (ConcretePlaquette physicalClayDimension L),
    ∃ deleted :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
      ∀ {X : Finset (ConcretePlaquette physicalClayDimension L)}
        (hk : 2 ≤ k)
        (hX : X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
          physicalClayDimension L root k),
        deleted X ∈ X ∧
          deleted X ≠ root ∧
          X.erase (deleted X) ∈
            plaquetteGraphPreconnectedSubsetsAnchoredCard
              physicalClayDimension L root (k - 1) ∧
          ∃ portalX, portal (X.erase (deleted X)) = some portalX ∧
          parentOf X ∈ X.erase (deleted X) ∧
          parentOf X ∈
            (plaquetteGraph physicalClayDimension L).neighborFinset portalX ∧
          deleted X ∈
            (plaquetteGraph physicalClayDimension L).neighborFinset (parentOf X)
```

Bridge target:

```lean
PhysicalPlaquetteGraphPortalSupportedSafeDeletionOrientation1296
  -> PhysicalPlaquetteGraphSafeDeletionOrientationCodeBound1296
```

The bridge should:

1. define `essential` as the image of `parentOf` over each residual fiber;
2. use the portal-supported condition to prove `essential R ⊆ R`;
3. get the physical neighbor code `code : p -> q -> Fin 1296`;
4. define `orientCode R` by coding each parent from the residual portal;
5. prove `Function.Injective (orientCode R)` by restricting `code portal` to the
   local neighbor finset.

## Why This Avoids the Raw Frontier

The raw residual frontier of a row-shaped residual can grow with the residual
size, as recorded in `dashboard/f3_residual_parent_menu_growth_search.md`.

The portal-supported policy does not attempt to cover that raw frontier.  It
only chooses one safe deletion per current bucket and requires the selected
parent to lie in a single local shell around the residual portal.  The essential
menu is therefore:

```text
{ chosen parentOf X | X.erase (deleted X) = R }
```

not:

```text
{ all residual parents adjacent to all possible one-step extensions of R }
```

That distinction is the point of the policy.

## Remaining Mathematical Risk

The hard theorem is now the portal-supported existence claim:

```text
Every anchored current bucket admits at least one safe deletion whose residual
has a portal such that the deleted plaquette is adjacent to a residual parent in
the portal's local shell.
```

This may be false for a naive portal definition.  If so, the next task should
adjust the portal choice or strengthen the first product-symbol component; it
must not fall back to the raw frontier bound.

## Validation Status

No Lean file was edited by this scope.  No build was required.  No theorem,
ledger row, or project percentage is upgraded.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.

## Recommended Next Task

```text
CODEX-F3-PORTAL-SUPPORTED-ORIENTATION-INTERFACE-001
```

Objective: add the Lean `Prop`
`PhysicalPlaquetteGraphPortalSupportedSafeDeletionOrientation1296` and, if it
builds without `sorry`, prove the bridge to
`PhysicalPlaquetteGraphSafeDeletionOrientationCodeBound1296`.
