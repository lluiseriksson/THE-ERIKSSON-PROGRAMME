# F3 Essential Frontier Menu Lemma Scope

Timestamp: 2026-04-27T07:40:00Z

Task: `CODEX-F3-ESSENTIAL-FRONTIER-MENU-LEMMA-SCOPE-001`

## Purpose

The v2.79 growth diagnostic ruled out the cheap path: the raw one-step frontier
of a residual bucket can grow with the residual size. A proof of
`PhysicalPlaquetteGraphResidualParentMenuBound1296` therefore cannot come from
the local degree bound for one fixed parent, nor from bounding all raw one-step
extensions of a residual.

This note scopes a narrower, Lean-stable route: bound only the parent candidates
that are actually selected by a canonical safe-deletion policy. This creates an
essential frontier, not the whole residual frontier.

No Lean theorem is added by this scope. No empirical result is treated as proof.

## Existing Target

The current open Lean proposition is:

```lean
PhysicalPlaquetteGraphResidualParentMenuBound1296
```

It already implies:

```lean
PhysicalPlaquetteGraphResidualParentMenuCovers1296
```

via:

```lean
physicalPlaquetteGraphResidualParentMenuCovers1296_of_residualParentMenuBound1296
```

That bridge is already proved. The missing content is the bound itself.

## Why Raw Frontier Is Too Large

The v2.79 diagnostic found the 2D row pattern:

```text
R_n = { (0,0), (0,1), ..., (0,n-1) }
```

If the menu must cover every one-step extension above the row, then it needs
`n` distinct parents. This proves only a diagnostic fact, not a Lean theorem,
but it is enough to prevent a bad proof plan: do not try to prove a uniform
bound on the whole raw one-step residual frontier.

The useful frontier must be smaller:

```text
raw residual frontier
  ⊇ safe-extension frontier
  ⊇ essential safe-deletion parent image
```

Only the last set is a plausible `≤ 1296` target.

## Proposed Lean Names

The next Lean interface should introduce names along these lines:

```lean
def PhysicalPlaquetteGraphCanonicalSafeDeletionChoice1296 : Prop := ...

def PhysicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296 : Prop := ...
```

The first proposition should supply canonical choice functions, not a bounded
menu:

```lean
choiceDeleted :
  {X : Finset (ConcretePlaquette physicalClayDimension L) //
    X ∈ plaquetteGraphPreconnectedSubsetsAnchoredCard
      physicalClayDimension L root k ∧ 2 ≤ k} →
  ConcretePlaquette physicalClayDimension L

choiceParent :
  (X : anchored-current-bucket) →
  ConcretePlaquette physicalClayDimension L
```

with proofs that, for each current bucket `X`,

- `choiceDeleted X ∈ X`,
- `choiceDeleted X ≠ root`,
- `X.erase (choiceDeleted X)` is an anchored residual bucket of card `k - 1`,
- `choiceParent X ∈ X.erase (choiceDeleted X)`,
- `choiceDeleted X` is adjacent to `choiceParent X`.

The second proposition should bound the image of `choiceParent` over each fixed
canonical residual:

```lean
∀ residual,
  (Finset.image choiceParent
    (current buckets X whose canonical residual is residual)).card ≤ 1296
```

This is structurally different from `PhysicalPlaquetteGraphResidualParentMenuBound1296`:
it first defines one canonical safe deletion per current bucket, then bounds the
image of the chosen parents over a residual fiber. It does not demand coverage
of every raw one-step extension of the residual.

## Exact Bridge To Existing Bound

The bridge should be named:

```lean
physicalPlaquetteGraphResidualParentMenuBound1296_of_essentialSafeDeletionParentFrontierBound1296
```

Expected type:

```lean
theorem physicalPlaquetteGraphResidualParentMenuBound1296_of_essentialSafeDeletionParentFrontierBound1296
    (hessential : PhysicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296) :
    PhysicalPlaquetteGraphResidualParentMenuBound1296 := ...
```

Proof idea:

1. For fixed `root` and `k`, obtain canonical safe-deletion data and the per
   residual image-cardinality bound from `hessential`.
2. Define `menu residual` to be the image of `choiceParent` over current buckets
   whose canonical erased residual is `residual`.
3. `menu residual ⊆ residual` follows from the `choiceParent` witness proof.
4. `(menu residual).card ≤ 1296` is exactly the essential-frontier bound.
5. For each current bucket `X`, choose its canonical deleted vertex and parent.
   By construction, the parent lies in `menu (X.erase z)` and is adjacent to
   `z`, producing the witness required by
   `PhysicalPlaquetteGraphResidualParentMenuBound1296`.

The full bridge chain then remains:

```text
PhysicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296
  -> PhysicalPlaquetteGraphResidualParentMenuBound1296
  -> PhysicalPlaquetteGraphResidualParentMenuCovers1296
  -> PhysicalPlaquetteGraphSymbolicResidualParentSelector1296
  -> PhysicalPlaquetteGraphDeletedVertexDecoderStep1296x1296
```

The last step is still the strengthened product-symbol route. It does not claim
the original `Fin 1296` decoder constant.

## Non-Circularity Check

This scope does not simply restate
`PhysicalPlaquetteGraphResidualParentMenuBound1296`:

- The current bound quantifies directly over an arbitrary residual menu.
- The proposed essential-frontier lemma first chooses a canonical safe deletion
  and parent for each current bucket.
- The bounded set is then a residual fiber image of that canonical parent map.
- The key mathematical work becomes proving that these canonical parent images
  have cardinality at most `1296`.

That image-cardinality statement is the new structural content.

## Remaining Mathematical Question

The hard question is now:

```text
Can the canonical safe-deletion policy be chosen so that, for every residual R,
the set of chosen reconstruction parents over all current buckets erasing to R
has cardinality at most 1296?
```

If yes, the bound follows through the bridge above.

If no, the product symbol must be strengthened again so that the first component
encodes a larger residual-parent branch than `Fin 1296`, or the decoder must use
a different canonical deletion policy.

## Recommended Next Task

Recommended next Codex task:

```text
CODEX-F3-ESSENTIAL-FRONTIER-BRIDGE-INTERFACE-001
```

Goal: add only the Lean `Prop` interface and the bridge theorem skeleton if it
builds without `sorry`. If the bridge is not yet stable, keep it dashboard-only.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No percentage or ledger status moves.
