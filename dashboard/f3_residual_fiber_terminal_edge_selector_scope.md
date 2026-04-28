# F3 residual-fiber canonical terminal-edge selector scope v2.135

Task: `CODEX-F3-RESIDUAL-FIBER-TERMINAL-EDGE-SELECTOR-SCOPE-001`

## Scope Result

The next Lean-stable target should be a structural selector, not another direct
attempt at the v2.132 image-bound interface:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalTerminalEdgeSelector1296
```

This target should factor the v2.134 blocker into explicit residual-local
terminal-edge data plus a selected-image bound.

## Proposed Contract Shape

The contract should quantify over the same v2.121 base-aware bookkeeping data
used by:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296
```

For each residual fiber and each essential parent `p`, it should provide:

- a residual-local canonical path or path code whose endpoint is `p`;
- a terminal-edge extraction operation from that path;
- a selected predecessor `terminalPred residual p` lying in the residual;
- terminal-edge adjacency
  `p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset
    (terminalPred residual p).1`
  whenever `residual.card ≠ 1`;
- residual path evidence from the selected predecessor to `p`;
- a selected-image bound
  ```lean
  (essential residual).image
    (fun p => (terminalPred residual ⟨p, hp⟩).1)
  ```
  has cardinality `<= 1296`, preferably via an injective `Fin 1296` code for
  selected terminal predecessors.

The selected-image bound is the key mathematical content. It cannot be replaced
by a root-shell code, local neighbor code for one fixed plaquette, residual-size
bound, or raw frontier bound.

## Exact Bridge Target

The bridge should be:

```lean
physicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296_of_residualFiberCanonicalTerminalEdgeSelector1296
```

with target:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296
```

The bridge is intended to build each
`PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgeData` by repacking:

- the endpoint proof for `p`;
- the selected residual terminal predecessor;
- the residual walk/path evidence;
- the terminal-edge adjacency proof;
- the selected predecessor image-cardinality proof.

This bridge should be projection/repacking only. It should not construct the
terminal-edge selector by using deleted-vertex adjacency outside the residual or
by choosing a predecessor from a current `(X, deleted X)` witness.

## Why This Is Sharper Than v2.132

`PhysicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296` already
asks for complete canonical last-edge data and the image bound. The proposed
selector separates the proof burden into:

1. canonical residual path or path-code data;
2. extraction of the terminal predecessor from that data;
3. selected predecessor image-cardinality `<= 1296`.

That separation is the missing structure identified by v2.134.

## Non-Confusions

Root-shell reachability is not terminal-edge adjacency. A root-shell parent may
reach an essential parent, but it need not be the immediate predecessor adjacent
to that parent.

Local degree is not the image bound. `neighborFinset.card <= 1296` bounds a
single plaquette's neighbor shell, not the set of selected terminal predecessors
over an entire residual fiber.

Residual size is not the image bound. The contract must bound the selected
predecessor image even when the residual itself is larger.

Raw residual frontier growth is not the image bound. The route must select a
structured terminal predecessor menu rather than enumerate every frontier
candidate.

Deleted-vertex adjacency outside the residual is not terminal-predecessor data.
The selected predecessor must live in the residual, so the current safe-deletion
vertex from `(X, deleted X)` cannot serve as the terminal predecessor.

Bounded search evidence remains diagnostic only and is not proof.

## Validation

This is a dashboard-only scope. No Lean file was edited, so no `lake build` was
required for this task. The existing v2.133 bridge remains the downstream
projection route once the selector supplies
`PhysicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296`.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No ledger status, project percentage,
README metric, planner metric, or Clay-level claim moved.

## Recommended Next Task

Add the no-sorry Lean Prop/interface:

```lean
PhysicalPlaquetteGraphResidualFiberCanonicalTerminalEdgeSelector1296
```

and, only if it builds without `sorry`, prove:

```lean
physicalPlaquetteGraphResidualFiberCanonicalLastEdgeImageBound1296_of_residualFiberCanonicalTerminalEdgeSelector1296
```

The bridge should preserve the distinction between canonical terminal-edge
selection and selected-image cardinality.
