# F3 residual terminal-neighbor code-separation proof attempt (v2.158)

Task: `CODEX-F3-PROVE-TERMINAL-NEIGHBOR-CODE-SEPARATION-001`

## Result

Attempted to prove:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborCodeSeparation1296
```

No Lean proof was added.  The current interfaces name the selected terminal
neighbor and carry a `terminalNeighborCode : Fin 1296` inside
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData`, but they do
not prove that this code separates the selected terminal-neighbor image.

## Exact No-Closure Blocker

The next missing theorem is a residual-fiber selector-code separation theorem,
tentatively:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorCodeSeparation1296
```

It should quantify over the same v2.121 bookkeeping inputs as
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborCodeSeparation1296` and
construct:

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

plus a genuine selector-code separation clause:

```lean
∀ residual
  (p q : {p : ConcretePlaquette physicalClayDimension L //
    p ∈ essential residual}),
  (terminalNeighborSelectorEvidence residual p).terminalNeighborCode =
    (terminalNeighborSelectorEvidence residual q).terminalNeighborCode →
  (terminalNeighborOfParent residual p).1 =
    (terminalNeighborOfParent residual q).1
```

This pairwise separation is the missing mathematical fact that would make the
existing `terminalNeighborCode` field load-bearing.  A bridge can then define
the `Fin 1296` code on the selected image by choosing a parent witness for each
image element and use the pairwise separation clause to prove injectivity; the
selected-image cardinality bound must also be supplied or derived from that
injective finite code.

## Why Existing Data Does Not Close It

* `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` contains a
  `terminalNeighborCode : Fin 1296`, but this is only a per-witness field.
  There is no theorem saying equal codes imply equal selected terminal
  neighbors.
* `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorImageBound1296`
  would be enough to build an injective code by `finsetCodeOfCardLe`, but that
  theorem itself remains unproved.
* Local degree bounds control the neighbor finset of one fixed plaquette only.
  They do not separate the selected image over all essential parents in a
  residual fiber.
* Residual walks, path splitting, and root/root-shell reachability provide
  path evidence, not injectivity of terminal-neighbor codes.
* v2.121 base-aware bookkeeping gives `deleted`, `parentOf`, `essential`,
  essential image identity, and essential subset residual.  Its adjacency fact
  concerns the deleted vertex outside the residual, not a residual terminal
  neighbor selected inside the residual.
* Packing/projection of an already bounded menu applies only after a bounded
  selected image has been constructed.

## Stop-Condition Check

Closing `PhysicalPlaquetteGraphResidualFiberTerminalNeighborCodeSeparation1296`
from the current ingredients would require one of the forbidden substitutions:

* post-hoc terminal neighbors chosen from a current `(X, deleted X)` witness;
* treating local degree, residual path existence, root-shell reachability,
  residual size, raw frontier, deleted-vertex adjacency, empirical search, or
  packing/projection as selected-image separation;
* using the `terminalNeighborCode` field without a theorem proving it separates
  selected terminal-neighbor values.

Therefore the correct outcome is no closure and the sharper selector-code
separation target above.

## Validation

```text
lake build YangMills.ClayCore.LatticeAnimalCount
```

passed.

No new theorem was introduced by this attempt, so no new theorem-specific axiom
trace was needed.  The v2.157 bridge trace remains:

```text
[propext, Classical.choice, Quot.sound]
```

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No status, percentage, README metric,
planner metric, ledger row, or Clay-level claim moved.

## Next Task

Scope the selector-code separation theorem:

```text
CODEX-F3-TERMINAL-NEIGHBOR-SELECTOR-CODE-SEPARATION-SCOPE-001
```
