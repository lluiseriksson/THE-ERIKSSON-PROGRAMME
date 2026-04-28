# F3 residual terminal-neighbor selector-code separation scope (v2.159)

Task: `CODEX-F3-TERMINAL-NEIGHBOR-SELECTOR-CODE-SEPARATION-SCOPE-001`

## Result

Scoped the next Lean-stable target behind the v2.157 selected-image
code-separation interface:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorCodeSeparation1296
```

Intended projection bridge:

```lean
physicalPlaquetteGraphResidualFiberTerminalNeighborCodeSeparation1296_of_residualFiberTerminalNeighborSelectorCodeSeparation1296
```

Bridge target:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalNeighborCodeSeparation1296
```

## Proposed Interface Shape

The theorem should quantify over the same v2.121 bookkeeping inputs used by
`PhysicalPlaquetteGraphResidualFiberTerminalNeighborCodeSeparation1296`:
`root`, `k`, `deleted`, `parentOf`, `essential`, the safe-deletion choice, the
essential image identity, and the essential subset residual hypothesis.

It should construct residual-local selector data:

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

and the load-bearing selector-code separation clause:

```lean
∀ residual
  (p q : {p : ConcretePlaquette physicalClayDimension L //
    p ∈ essential residual}),
  (terminalNeighborSelectorEvidence residual p).terminalNeighborCode =
    (terminalNeighborSelectorEvidence residual q).terminalNeighborCode →
  (terminalNeighborOfParent residual p).1 =
    (terminalNeighborOfParent residual q).1
```

For the bridge into v2.157, the interface should also expose either:

```lean
∀ residual,
  ((essential residual).attach.image
    (fun p => (terminalNeighborOfParent residual p).1)).card ≤ 1296
```

or a narrow local finite-card lemma deriving that bound from the pairwise
`Fin 1296` selector-code separation.  The preferred Lean-stable shape is to
carry the selected-image card bound in this interface, with a later proof free
to obtain it from the separation clause.

## Bridge Sketch

Given `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorCodeSeparation1296`:

1. Reuse `terminalNeighborOfParent` and `terminalNeighborSelectorEvidence`.
2. For every selected terminal-neighbor image element, choose a parent witness
   from `Finset.mem_image` using classical choice.
3. Define `terminalNeighborImageCode residual q` as the chosen witness's
   `terminalNeighborCode`.
4. Prove injectivity of `terminalNeighborImageCode` by unpacking the chosen
   parent witnesses and applying the selector-code separation clause.
5. Supply the selected-image cardinality bound from the interface, or from the
   separate finite-card lemma if that route is chosen.

This bridge only repackages a selector-code separation theorem into the v2.157
image-code interface.  It does not choose terminal neighbors from a current
`(X, deleted X)` witness.

## Non-Substitutes

This target is not closed by:

* the per-witness existence of `terminalNeighborCode : Fin 1296`;
* local degree of one fixed plaquette;
* residual path existence or path splitting;
* root or root-shell reachability;
* residual size or raw residual frontier;
* deleted-vertex adjacency outside the residual;
* empirical bounded search;
* packing or projection of an already bounded menu.

The point of the theorem is exactly the missing pairwise separation fact:
equal selector codes must force equal selected terminal-neighbor values across
essential parents in the same residual fiber.

## Validation

This is a dashboard-only scope artifact.  No Lean file was edited and no
`lake build` was required.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`.  No status, percentage, README metric,
planner metric, ledger row, or Clay-level claim moved.

## Next Task

Add the no-sorry Lean interface and projection bridge:

```text
CODEX-F3-TERMINAL-NEIGHBOR-SELECTOR-CODE-SEPARATION-INTERFACE-001
```
