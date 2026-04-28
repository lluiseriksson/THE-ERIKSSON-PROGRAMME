# F3 residual-fiber terminal-predecessor image bound scope v2.128

Task: `CODEX-F3-RESIDUAL-FIBER-TERMINAL-PREDECESSOR-IMAGE-BOUND-SCOPE-001`

## Purpose

The v2.127 proof attempt showed that
`PhysicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296` cannot be
proved from the current v2.121 bookkeeping API alone.  The missing ingredient is
not the v2.124 packing theorem and not the base-aware `deleted`/`parentOf`
bookkeeping.  It is a residual-fiber selected terminal-predecessor image bound.

This scope isolates that missing ingredient so the next Lean task can add a
stable Prop/interface without merely restating the full v2.126 producer.

## Recommended Lean target

Recommended name:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296
```

Intended shape:

```lean
def PhysicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : ℕ)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    -- same v2.121 bookkeeping hypotheses used by v2.126:
    bookkeepingChoice deleted parentOf essential →
    bookkeepingImage essential parentOf deleted →
    bookkeepingEssentialSubset essential →
      ∃ terminalPredOfParent :
        ∀ residual,
          {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual} →
            {q : ConcretePlaquette physicalClayDimension L // q ∈ residual},
        (∀ residual
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}),
          residual.card ≠ 1 →
            p.1 ∈ (plaquetteGraph physicalClayDimension L).neighborFinset
              (terminalPredOfParent residual p).1) ∧
        (∀ residual
          (p : {p : ConcretePlaquette physicalClayDimension L //
            p ∈ essential residual}),
          ∃ target : {r : ConcretePlaquette physicalClayDimension L //
              r ∈ residual},
            target.1 = p.1 ∧
              Nonempty
                (((plaquetteGraph physicalClayDimension L).induce
                  {x | x ∈ residual}).Walk
                    (terminalPredOfParent residual p) target)) ∧
        ∀ residual,
          ((essential residual).attach.image
            (fun p => (terminalPredOfParent residual p).1)).card ≤ 1296
```

The placeholders `bookkeepingChoice`, `bookkeepingImage`, and
`bookkeepingEssentialSubset` should be replaced with the exact hypotheses used
by `PhysicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296`.

## Exact Bridge Back To v2.126

The bridge target should be:

```lean
physicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296_of_residualFiberTerminalPredecessorImageBound1296
```

Bridge inputs:

1. `PhysicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296`;
2. the same v2.121 bookkeeping hypotheses already quantified by
   `PhysicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296`.

Bridge construction:

For each residual, define:

```lean
terminalPredMenu residual =
  (essential residual).attach.image
    (fun p => (terminalPredOfParent residual p).1)
```

Then the selected-image theorem supplies:

- `terminalPredMenu ⊆ residual`, by subtype membership of
  `terminalPredOfParent`;
- the selected-image identity, by definition;
- menu membership for every selected predecessor, by `Finset.mem_image`;
- last-edge adjacency for non-singleton residuals;
- residual path evidence;
- `terminalPredMenu.card <= 1296`.

This repacks directly into the existential package required by
`PhysicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296`.

## Why This Is Sharper Than v2.126

The full v2.126 producer already packages the menu, selector, adjacency, path
evidence, and cardinality bound.  The new target factors the construction into
one residual-indexed selector plus a selected-image bound.  The menu is then
derived mechanically as the selector image.

That separation prevents the next proof from hiding the hard part in a
post-hoc menu choice.  The load-bearing theorem is explicitly:

```text
the image of the residual-local terminal predecessor selector has card <= 1296
```

## Non-confusions

This target is not the v2.121 deleted-vertex adjacency clause.  In v2.121,
`deleted X` is adjacent to `parentOf X`, but `deleted X` is outside
`X.erase (deleted X)` and therefore cannot be the terminal predecessor required
inside the residual.

This target is not a raw residual frontier bound.  It only bounds the image of
the selected terminal-predecessor map.

This target is not a residual-cardinality bound.  The residual may be large;
only the chosen predecessor image is bounded.

This target is not the local degree bound of one fixed plaquette.  The selected
image is indexed by an entire residual fiber of essential parents.

This target is not first-shell/root reachability.  It needs last-edge adjacency
to each essential parent, plus induced residual path evidence.

The v2.109 finite search is only diagnostic evidence.  It must not be used as
proof of this target.

## Recommended next task

```text
CODEX-F3-RESIDUAL-FIBER-TERMINAL-PREDECESSOR-IMAGE-BOUND-INTERFACE-001
```

Add the no-sorry Lean Prop/interface
`PhysicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296` and, only
if it builds without sorry, the bridge
`physicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296_of_residualFiberTerminalPredecessorImageBound1296`.

## Validation

This is a dashboard-only scope.  No Lean file was edited, so no `lake build`
was required.

## Non-claims

This task does not prove:

- `PhysicalPlaquetteGraphResidualFiberTerminalPredecessorImageBound1296`;
- `PhysicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296`;
- `PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`;
- any decoder theorem or compression to older constants.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No ledger status, project percentage,
README metric, planner metric, or Clay-level claim moved.
