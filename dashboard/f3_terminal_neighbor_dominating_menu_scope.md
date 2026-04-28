# F3 residual terminal-neighbor dominating-menu scope (v2.153)

Task: `CODEX-F3-TERMINAL-NEIGHBOR-DOMINATING-MENU-SCOPE-001`

## Result

Scoped the sharper residual-fiber bounded-menu target:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296
```

with intended bridge:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborImageCompression1296_of_residualFiberTerminalNeighborDominatingMenu1296
```

Bridge conclusion:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborImageCompression1296
```

No Lean file was edited for this scope.

## Proposed Shape

The theorem should quantify over the same v2.121 bookkeeping fiber data used by
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborImageCompression1296`:
`root`, `k`, `deleted`, `parentOf`, `essential`, plus the safe-deletion choice,
essential image identity, and essential subset residual hypotheses.

For each residual fiber it must first construct a bounded residual-local menu:

```lean
terminalNeighborMenu :
  Finset (ConcretePlaquette physicalClayDimension L) →
    Finset (ConcretePlaquette physicalClayDimension L)

terminalNeighborMenu residual ⊆ residual
(terminalNeighborMenu residual).card ≤ 1296
```

Then, for every essential parent, it must prove domination by that menu:

```lean
∀ residual,
  (p : {p : ConcretePlaquette physicalClayDimension L //
    p ∈ essential residual}) →
    ∃ q : {q : ConcretePlaquette physicalClayDimension L //
      q ∈ terminalNeighborMenu residual},
      PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
        residual p.1
        ⟨q.1, hmenu_subset residual q.2⟩
```

The selected terminal-neighbor function is not part of the primitive burden.
It is derived in the bridge by choosing from the menu-domination evidence.  This
keeps the load-bearing statement focused on constructing the bounded menu and a
residual-local domination relation.

## Bridge Sketch

Given `hdom :
PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296`, the
bridge to v2.151 should:

1. obtain `terminalNeighborMenu`, `hmenu_subset`, `hmenu_card`, and
   `hdominating`;
2. define

```lean
terminalNeighborOfParent residual p :=
  ⟨(Classical.choose (hdominating residual p)).1,
    hmenu_subset residual (Classical.choose (hdominating residual p)).2⟩
```

3. define selector evidence from `Classical.choose_spec`;
4. prove selector membership in the menu from the chosen subtype proof;
5. prove selected image subset the menu by unpacking `Finset.mem_image`.

The bridge therefore supplies
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborImageCompression1296`
without constructing a menu from local degree, path existence, root-shell data,
residual size, raw frontier growth, deleted-vertex adjacency, empirical search,
or packing/projection alone.

## Why This Is Sharper Than v2.151

`PhysicalPlaquetteGraphResidualFiberTerminalNeighborImageCompression1296`
already asks for:

* a bounded `terminalNeighborMenu`;
* a selector into the residual;
* selector membership in the menu;
* selector evidence;
* selected image subset the menu.

The dominating-menu theorem isolates the missing constructive burden: build the
bounded menu first and prove it dominates all essential parents by residual-local
terminal-neighbor evidence.  The selector and image-cover clauses become
mechanical choices from that domination relation.

This is not merely restating v2.151, because the proposed primitive data is a
menu plus a domination relation, not a selected image or selector-cardinality
claim.

## Non-Substitutes

The dominating-menu theorem is not supplied by:

* local neighbor existence for each parent, which gives no uniform menu;
* local degree of one fixed plaquette, which bounds one neighbor set only;
* residual path existence or first/terminal path splitting, which gives
  reachability but no bounded dominating menu;
* root or root-shell reachability/code bounds, which concern first-shell data
  from the root;
* residual size or raw residual frontier growth, which can be much larger than
  `1296`;
* deleted-vertex adjacency outside the residual, which is not terminal-neighbor
  data inside the residual;
* empirical bounded search, which is not proof;
* packing/projection of an already bounded menu, which only applies after this
  theorem has constructed the menu.

## Stop-Condition Check

This scope does not choose terminal neighbors post-hoc from a current
`(X, deleted X)` witness.  Any later selector is chosen only from the
residual-fiber domination relation supplied by the theorem.

It does not claim decoder compression, F3-COUNT progress, or any status or
percentage move.

## Validation

Dashboard-only scope. No Lean file was edited, so no `lake build` was required.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, ledger row, or Clay-level claim moved.

## Next Task

Add the Lean interface and projection bridge:

```text
CODEX-F3-TERMINAL-NEIGHBOR-DOMINATING-MENU-INTERFACE-001
```
