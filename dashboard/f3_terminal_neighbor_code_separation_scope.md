# F3 residual terminal-neighbor code-separation scope (v2.156)

Task: `CODEX-F3-TERMINAL-NEIGHBOR-CODE-SEPARATION-SCOPE-001`

## Result

Scoped the sharper residual-fiber selected-image target:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborCodeSeparation1296
```

with intended bridge:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296_of_residualFiberTerminalNeighborCodeSeparation1296
```

Bridge conclusion:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296
```

No Lean file was edited for this scope.

## Proposed Shape

The theorem should quantify over the same v2.121 bookkeeping fiber inputs used
by `PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296`:
`root`, `k`, `deleted`, `parentOf`, `essential`, plus the safe-deletion choice,
essential image identity, and essential subset residual hypotheses.

For each residual it must construct a residual-local selector and evidence:

```lean
terminalNeighborOfParent :
  ∀ residual,
    (p : {p : ConcretePlaquette physicalClayDimension L //
      p ∈ essential residual}) →
      {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}

terminalNeighborSelectorEvidence :
  ∀ residual,
    (p : {p : ConcretePlaquette physicalClayDimension L //
      p ∈ essential residual}) →
      PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData
        residual p.1 (terminalNeighborOfParent residual p)
```

Then it must expose selected-image code separation.  A Lean-stable form is:

```lean
selectedTerminalNeighborImage residual :=
  (essential residual).attach.image
    (fun p => (terminalNeighborOfParent residual p).1)

terminalNeighborImageCode :
  ∀ residual,
    {q : ConcretePlaquette physicalClayDimension L //
      q ∈ selectedTerminalNeighborImage residual} → Fin 1296

terminalNeighborImageCode_injective :
  ∀ residual,
    Function.Injective (terminalNeighborImageCode residual)
```

Equivalently, the interface may include the derived card bound:

```lean
∀ residual, (selectedTerminalNeighborImage residual).card ≤ 1296
```

but the load-bearing mathematical content should be the `Fin 1296` separation
or an equivalent injective code on the selected image.  The card bound alone is
acceptable only if the interface explains which separation theorem produced it.

## Bridge Sketch

Given
`hsep : PhysicalPlaquetteGraphResidualFiberTerminalNeighborCodeSeparation1296`,
the bridge into
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296` should:

1. obtain `terminalNeighborOfParent`, `terminalNeighborSelectorEvidence`, and
   selected-image code separation;
2. define

```lean
terminalNeighborMenu residual :=
  (essential residual).attach.image
    (fun p => (terminalNeighborOfParent residual p).1)
```

3. prove `terminalNeighborMenu residual ⊆ residual` by unpacking
   `Finset.mem_image` and using the residual membership carried by
   `terminalNeighborOfParent residual p`;
4. derive `(terminalNeighborMenu residual).card ≤ 1296` from the injective
   `Fin 1296` code;
5. prove domination for each essential parent `p` by choosing
   `q = terminalNeighborOfParent residual p`, whose membership in the menu is
   immediate from `Finset.mem_image`, and wrap
   `terminalNeighborSelectorEvidence residual p` in `Nonempty`.

This bridge uses the selected image as the menu.  It therefore supplies the
menu-first domination theorem without post-hoc terminal-neighbor choices from a
current `(X, deleted X)` witness.

## Why This Is Sharper Than v2.154

`PhysicalPlaquetteGraphResidualFiberTerminalNeighborDominatingMenu1296` asks for
an already bounded menu plus a domination relation.  The code-separation target
isolates how such a menu is to be obtained: construct a residual-local selected
terminal neighbor for each essential parent, then prove the selected image has
only `1296` possible values via an injective code.

This is not merely restating v2.154.  The primitive burden is not an arbitrary
menu; it is a selected image together with a code-separation certificate.

## Non-Substitutes

The code-separation theorem is not supplied by:

* local degree of one fixed plaquette, which bounds one neighbor finset but not
  the selected image across all essential parents;
* residual paths or path splitting, which give reachability/evidence but not
  injectivity of a `Fin 1296` terminal-neighbor code;
* root or root-shell reachability/code bounds, which concern first-shell data
  from the anchored root, not terminal neighbors adjacent to essential parents;
* residual size or raw residual frontier growth, which can be much larger than
  `1296`;
* deleted-vertex adjacency outside the residual, which is not terminal-neighbor
  data inside the residual;
* empirical search, which is not proof;
* packing/projection of an already bounded menu, which only applies after the
  selected image has already been bounded.

## Stop-Condition Check

This scope does not choose terminal neighbors post-hoc from a current
`(X, deleted X)` witness.  Any selector in the target is residual-local data,
and the bound is a selected-image code-separation statement, not local degree,
root-shell reachability, residual size, raw frontier, deleted-vertex adjacency,
empirical search, or packing.

It does not claim decoder compression, F3-COUNT progress, or any status or
percentage move.

## Validation

Dashboard-only scope.  No Lean file was edited, so no `lake build` was
required.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, ledger row, or Clay-level claim moved.

## Next Task

Add the Lean interface and projection bridge:

```text
CODEX-F3-TERMINAL-NEIGHBOR-CODE-SEPARATION-INTERFACE-001
```
