# F3 Residual Parent-Menu Bound Attempt v2.78

Timestamp: 2026-04-27T06:55:00Z

Task: `CODEX-F3-PROVE-RESIDUAL-PARENT-MENU-BOUND-001`

## Target

Attempted target:

```lean
PhysicalPlaquetteGraphResidualParentMenuBound1296
```

This is the residual-frontier menu-size theorem isolated by v2.76/v2.77.  It is
stronger than the local neighbor-degree bound: it must bound, for each residual
bucket, the number of residual parent candidates needed to cover all safe
one-plaquette extensions of that residual.

## Lean Progress

The bound itself was not proved and was not refuted.

Codex did prove the conditional enumeration bridge:

```lean
physicalPlaquetteGraphResidualParentMenuCovers1296_of_residualParentMenuBound1296
```

Meaning:

```lean
PhysicalPlaquetteGraphResidualParentMenuBound1296
  -> PhysicalPlaquetteGraphResidualParentMenuCovers1296
```

The proof enumerates the bounded residual menu into `Fin 1296` using the existing
`finsetCodeOfCardLe` pattern.  This is bridge evidence only: it does not prove
that such a bounded residual-frontier menu exists.

Axiom trace:

```text
YangMills.physicalPlaquetteGraphResidualParentMenuCovers1296_of_residualParentMenuBound1296
depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Bounded Search

Codex added a small empirical script:

```text
scripts/f3_residual_parent_menu_bound_search.py
```

Command:

```powershell
python scripts\f3_residual_parent_menu_bound_search.py
```

Output:

```text
{'d': 2, 'L': 2, 'k': 2, 'vertices': 4, 'anchored_connected_buckets': 2, 'residual_variables': 1, 'max_residual_card': 1, 'searched_menu_size_up_to': 1, 'min_menu_size_found': 1, 'witness_assignment_size': 1}
{'d': 2, 'L': 2, 'k': 3, 'vertices': 4, 'anchored_connected_buckets': 3, 'residual_variables': 2, 'max_residual_card': 2, 'searched_menu_size_up_to': 2, 'min_menu_size_found': 2, 'witness_assignment_size': 2}
{'d': 2, 'L': 3, 'k': 3, 'vertices': 9, 'anchored_connected_buckets': 5, 'residual_variables': 2, 'max_residual_card': 2, 'searched_menu_size_up_to': 2, 'min_menu_size_found': 2, 'witness_assignment_size': 2}
{'d': 3, 'L': 2, 'k': 3, 'vertices': 24, 'anchored_connected_buckets': 109, 'residual_variables': 11, 'max_residual_card': 2, 'searched_menu_size_up_to': 2, 'min_menu_size_found': 2, 'witness_assignment_size': 11}
{'d': 4, 'L': 1, 'k': 3, 'vertices': 6, 'anchored_connected_buckets': 10, 'residual_variables': 5, 'max_residual_card': 2, 'searched_menu_size_up_to': 2, 'min_menu_size_found': 1, 'witness_assignment_size': 5}
{'d': 4, 'L': 2, 'k': 3, 'vertices': 96, 'anchored_connected_buckets': 838, 'residual_variables': 29, 'max_residual_card': 2, 'searched_menu_size_up_to': 2, 'min_menu_size_found': 2, 'witness_assignment_size': 29}
{'d': 2, 'L': 3, 'k': 4, 'vertices': 9, 'anchored_connected_buckets': 11, 'residual_variables': 5, 'max_residual_card': 3, 'searched_menu_size_up_to': 3, 'min_menu_size_found': 2, 'witness_assignment_size': 5}
```

Interpretation: the earlier square-corner obstruction forces menu size greater
than `1`, but the bounded cases above do not refute a small residual menu.  In
particular the physical `(d=4, L=2, k=3)` counterexample to a single parent is
covered by menu size `2`.

This empirical absence of a counterexample is not proof.

## Exact Remaining Blocker

The exact remaining theorem is still:

```lean
PhysicalPlaquetteGraphResidualParentMenuBound1296
```

The missing mathematical content is a structural bound:

```text
for every residual bucket R, the safe extensions relevant to anchored deletion
can be covered by at most 1296 parent candidates p ∈ R
```

This cannot be obtained by enumerating `R`, since `R.card = k - 1` and `k` is
arbitrary.  It also cannot be obtained from
`plaquetteGraph_neighborFinset_card_le_physical_ternary`, which bounds the
number of deleted vertices adjacent to one fixed parent, not the number of
parents required for one residual.

## Validation

Build:

```powershell
lake build YangMills.ClayCore.LatticeAnimalCount
```

Result:

```text
Build completed successfully (8184 jobs).
```

No `sorry`.  No new project axiom.  The new bridge theorem has the allowed axiom
trace `[propext, Classical.choice, Quot.sound]`.

## Project Status

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  No old `Fin 1296` decoder contract is
claimed, and no strengthened product-symbol constant is moved.  No Clay,
lattice, honest-discount, named-frontier, README, or planner percentage moved.

Recommended next task:

```text
CODEX-F3-RESIDUAL-PARENT-MENU-GROWTH-SEARCH-001
```
