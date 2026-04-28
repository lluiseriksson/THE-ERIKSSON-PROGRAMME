# F3 Safe-Deletion Orientation Indegree Scope

Timestamp: 2026-04-27T08:30:00Z

Task: `CODEX-F3-SAFE-DELETION-ORIENTATION-INDEGREE-SCOPE-001`

## Purpose

The v2.82 attempt isolated the next real obstruction below
`PhysicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296`: a
bounded-indegree orientation of safe deletions.

This task scopes that orientation theorem. No Lean theorem is added here,
because the obvious Lean statement would merely repackage the v2.81 essential
frontier proposition unless it also carries a separate finite coding or
injectivity structure.

## Existing Open Target

The current bridge target is:

```lean
PhysicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296
```

It already asks for:

- a canonical deleted plaquette `deleted X`,
- a canonical parent `parentOf X`,
- an essential residual menu equal to the image of `parentOf` over each residual
  fiber,
- and a direct `card ≤ 1296` bound on that menu.

Therefore a new proposition that merely says "choose deleted/parentOf with
fiber image card at most 1296" would be definitionally or morally the same
target, triggering the stop condition.

## Stable Non-Circular Shape

The next Lean-stable proposition should add a separate orientation-code witness:

```lean
PhysicalPlaquetteGraphSafeDeletionOrientationCodeBound1296
```

Suggested structure:

```lean
def PhysicalPlaquetteGraphSafeDeletionOrientationCodeBound1296 : Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ),
    ∃ deleted :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L,
    ∃ orientCode :
      Finset (ConcretePlaquette physicalClayDimension L) → Fin 1296,
      -- safe-deletion and parent adjacency clauses
      ... ∧
      -- residual-fiber code separates distinct chosen parents
      ∀ {X Y},
        X ∈ anchoredCard root k →
        Y ∈ anchoredCard root k →
        X.erase (deleted X) = Y.erase (deleted Y) →
        parentOf X ≠ parentOf Y →
        orientCode X ≠ orientCode Y
```

This is not the same as the essential frontier proposition:

- It does not directly postulate a bounded menu.
- It asks for a `Fin 1296` orientation code on current buckets.
- The code must separate distinct chosen parents inside each residual fiber.
- The menu bound is then derived by injecting the chosen-parent image into
  `Fin 1296`.

## Exact Bridge

The bridge should be:

```lean
physicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296_of_safeDeletionOrientationCodeBound1296
```

Expected type:

```lean
PhysicalPlaquetteGraphSafeDeletionOrientationCodeBound1296
  -> PhysicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296
```

Proof idea:

1. Define `essential residual` as the image of `parentOf` over the residual
   fiber, exactly as in v2.81.
2. Safe-deletion clauses supply the deleted vertex, residual membership, parent
   membership, and adjacency clauses.
3. To prove `(essential residual).card ≤ 1296`, use the `orientCode` separation
   clause to inject the parent image over that residual fiber into `Fin 1296`.
4. Use `Fintype.card (Fin 1296) = 1296`.

The missing technical Lean work is not mathematical search; it is setting up the
finite-image injection cleanly enough that the bridge compiles without `sorry`.

## Why Raw Frontier Growth Is Avoided

The v2.79 row residual shows that the raw one-step frontier can require `n`
parents. The orientation-code theorem does not cover the raw frontier. It only
codes the parents selected by the canonical safe-deletion orientation.

This is the intended narrowing:

```text
raw residual frontier                  can grow
all possible safe-extension parents     may grow
chosen orientation parent image         target: injects into Fin 1296
```

## No-Closure Statement

This task does not prove the orientation theorem. It scopes the next Lean
interface that can avoid restating the essential frontier bound.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No status, percentage, or Clay claim
moves from this scope.

## Recommended Next Task

Recommended next Codex task:

```text
CODEX-F3-SAFE-DELETION-ORIENTATION-CODE-INTERFACE-001
```

Objective: add `PhysicalPlaquetteGraphSafeDeletionOrientationCodeBound1296` and
the bridge to `PhysicalPlaquetteGraphEssentialSafeDeletionParentFrontierBound1296`
if the finite-image injection proof builds without `sorry`.
