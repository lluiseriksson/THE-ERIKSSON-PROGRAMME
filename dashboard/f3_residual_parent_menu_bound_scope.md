# F3 Residual Parent-Menu Bound Scope

Timestamp: 2026-04-27T06:15:00Z

Task: `CODEX-F3-RESIDUAL-PARENT-MENU-BOUND-SCOPE-001`

## Lean Contract Added

Codex added the stable proposition:

```lean
PhysicalPlaquetteGraphResidualParentMenuBound1296
```

Location:

```text
YangMills/ClayCore/LatticeAnimalCount.lean
```

The proposition asks for, for every physical `root` and cardinality `k`, a
residual-only finite menu:

```lean
menu :
  Finset (ConcretePlaquette physicalClayDimension L) ->
  Finset (ConcretePlaquette physicalClayDimension L)
```

with:

```lean
menu residual ⊆ residual
(menu residual).card ≤ 1296
```

and enough coverage that every current anchored bucket has a safe deleted
plaquette adjacent to some parent in the menu of its residual.

## What This Separates

This bound is not the existing local branching theorem:

```lean
plaquetteGraph_neighborFinset_card_le_physical_ternary
```

That theorem controls:

```text
for one fixed parent p, at most 1296 neighboring deleted plaquettes z
```

The new target controls:

```text
for one fixed residual R, at most 1296 parent candidates p ∈ R cover all safe
one-plaquette extensions R ∪ {z}
```

These are different directions.  The v2.76 no-closure came from exactly this
direction mismatch.

## Plausibility / Risk

Status: `OPEN_PLAUSIBILITY_UNKNOWN`.

The bound is plausible only if the relevant safe extensions of a residual can be
covered by a uniformly local frontier of parents.  It is not justified by
enumerating the residual, because the residual has cardinality `k - 1` and `k`
is arbitrary.

The square-corner counterexample in
`dashboard/f3_residual_selector_counterexample_search.md` refutes a single
residual-only parent choice, but it does not refute a 1296-entry residual menu.
For the square-corner pattern, a two-parent menu would already cover the local
ambiguity.  The remaining question is whether a uniform 1296-parent menu always
suffices for arbitrary residuals.

## Handoff

If `PhysicalPlaquetteGraphResidualParentMenuBound1296` is proved, the next
implementation step is a bridge:

```lean
PhysicalPlaquetteGraphResidualParentMenuBound1296
  -> PhysicalPlaquetteGraphResidualParentMenuCovers1296
```

That bridge should enumerate the bounded menu into `Fin 1296 -> Option parent`
using the existing `finsetCodeOfCardLe` pattern.  It should be proved only after
the menu-bound theorem is available or assumed as an explicit hypothesis.

If the bound is false, the first product-symbol component must be strengthened
beyond `Fin 1296`; the honest migration path is a parent-menu alphabet sized by
a proved residual-frontier bound, followed by a separate Cowork constants audit.

## Validation

Build:

```powershell
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result:

```text
Build completed successfully (8184 jobs).
```

No theorem was added for the new proposition.  No `sorry`.  No new project
axiom.

## Project Status

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  No old `Fin 1296` decoder contract is
claimed.  No strengthened product-symbol downstream constant is claimed.  No
Clay, lattice, honest-discount, named-frontier, README, or planner percentage
moved.

Recommended next task:

```text
CODEX-F3-PROVE-RESIDUAL-PARENT-MENU-BOUND-001
```
