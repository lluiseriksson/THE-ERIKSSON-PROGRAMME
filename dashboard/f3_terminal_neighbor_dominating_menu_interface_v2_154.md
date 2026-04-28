# F3 residual terminal-neighbor dominating-menu interface (v2.154)

Task: `CODEX-F3-TERMINAL-NEIGHBOR-DOMINATING-MENU-INTERFACE-001`

## Result

Added the Lean interface:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296
```

and the no-sorry bridge:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborImageCompression1296_of_residualFiberTerminalNeighborDominatingMenu1296
```

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborImageCompression1296
```

## Interface Shape

The interface is menu-first.  For the same v2.121 bookkeeping fiber inputs used
by the v2.151 compression interface, it asks for:

```lean
terminalNeighborMenu :
  Finset (ConcretePlaquette physicalClayDimension L) →
    Finset (ConcretePlaquette physicalClayDimension L)

hmenu_subset : ∀ residual, terminalNeighborMenu residual ⊆ residual
∀ residual, (terminalNeighborMenu residual).card ≤ 1296
```

and then a domination relation:

```lean
∀ residual,
  (p : {p : ConcretePlaquette physicalClayDimension L //
    p ∈ essential residual}) →
    ∃ q : {q : ConcretePlaquette physicalClayDimension L //
      q ∈ terminalNeighborMenu residual},
      Nonempty
        (PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
          residual p.1 ⟨q.1, hmenu_subset residual q.2⟩)
```

The `Nonempty` wrapper is necessary because
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` is a
`structure` in `Type`, not a `Prop`.

## Bridge

The bridge chooses the selector from the domination relation:

* `terminalNeighborOfParent residual p` is the chosen menu element, coerced into
  the residual by `hmenu_subset`.
* selector evidence is extracted from the `Nonempty` witness by
  `Classical.choice`;
* selector membership in the menu follows from the chosen subtype proof;
* selected-image subset the menu follows by unpacking `Finset.mem_image`.

This is not a post-hoc choice from a current `(X, deleted X)` witness.  The
choice is only from the residual-fiber domination relation supplied by the new
interface.

## Non-Substitutes

The interface and bridge do not use local degree, residual path
existence/splitting, root/root-shell reachability, residual size, raw frontier
growth, deleted-vertex adjacency outside the residual, empirical search, or
packing/projection of an already bounded menu as proof of the selected-image
bound.

## Validation

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

passed.

The new bridge axiom trace is:

```text
[propext, Classical.choice, Quot.sound]
```

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, ledger row, or Clay-level claim moved.

## Next Task

Prove or precisely fail the dominating-menu theorem:

```text
CODEX-F3-PROVE-TERMINAL-NEIGHBOR-DOMINATING-MENU-001
```
