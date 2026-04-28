# F3 residual-fiber terminal-predecessor domination scope v2.125

Task: `CODEX-F3-RESIDUAL-FIBER-TERMINAL-PREDECESSOR-DOMINATION-SCOPE-001`

## Purpose

The v2.124 theorem
`physicalPlaquetteGraph_residualDominatedTerminalPredecessorPacking1296`
closed only the packing step: an explicit selected terminal-predecessor menu
with `terminalPredMenu.card <= 1296` packs into an injective `Fin 1296` code.

The missing producer must now supply those explicit menu data for the
residual fibers arising from the proved v2.121 bookkeeping theorem.  It must
not return to the too-strong v2.114 shape where arbitrary
`essential subset residual` data was treated as enough to force last-edge
domination.

## Recommended Lean target

Recommended name:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296
```

Intended scope:

```lean
def PhysicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296 :
    Prop :=
  ∀ {L : Nat} [NeZero L]
    (root : ConcretePlaquette physicalClayDimension L) (k : Nat)
    (deleted parentOf :
      Finset (ConcretePlaquette physicalClayDimension L) →
        ConcretePlaquette physicalClayDimension L)
    (essential :
      Finset (ConcretePlaquette physicalClayDimension L) →
        Finset (ConcretePlaquette physicalClayDimension L)),
    -- v2.121 bookkeeping clauses, not arbitrary residual data:
    bookkeepingChoice deleted parentOf →
    bookkeepingImage essential parentOf deleted →
    bookkeepingEssentialSubset essential →
      ∀ residual,
        ∃ terminalPredMenu,
        ∃ terminalPredOfParent :
          {p // p ∈ essential residual} → {q // q ∈ residual},
          terminalPredMenu ⊆ residual ∧
          terminalPredMenu =
            (essential residual).attach.image
              (fun p => (terminalPredOfParent p).1) ∧
          (∀ p, (terminalPredOfParent p).1 ∈ terminalPredMenu) ∧
          (residual.card ≠ 1 →
            ∀ p, p.1 ∈
              (plaquetteGraph physicalClayDimension L).neighborFinset
                (terminalPredOfParent p).1) ∧
          (∀ p,
            ∃ target : {r // r ∈ residual},
              target.1 = p.1 ∧
              Nonempty
                (((plaquetteGraph physicalClayDimension L).induce
                  {x | x ∈ residual}).Walk
                    (terminalPredOfParent p) target)) ∧
          terminalPredMenu.card <= 1296
```

The placeholder `bookkeepingChoice`, `bookkeepingImage`, and
`bookkeepingEssentialSubset` should be replaced by the actual v2.116/v2.121
clauses in the Lean interface.  The important point is that the producer is
indexed by the base-aware bookkeeping data `deleted`, `parentOf`, and
`essential`, not by arbitrary residual/essential pairs.

## Bridge target

The exact bridge target should be:

```lean
physicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296_of_baseAwareBookkeeping_of_residualFiberTerminalPredecessorDomination1296_of_packing1296
```

Bridge inputs:

1. `PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296`,
   proved in v2.121 by
   `physicalPlaquetteGraph_baseAwareTerminalPredecessorBookkeeping1296`.
2. `PhysicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296`,
   the new producer target scoped here.
3. `PhysicalPlaquetteGraphResidualDominatedTerminalPredecessorPacking1296`,
   proved in v2.124 by
   `physicalPlaquetteGraph_residualDominatedTerminalPredecessorPacking1296`.

The bridge should unpack the v2.121 bookkeeping data for each `(root, k)`,
ask the producer for the residual-fiber terminal predecessor menu, apply the
v2.124 packing theorem to obtain the injective `Fin 1296` code, and repack
the fields required by `PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`.

## Migration from v2.114

Superseded target:

```lean
PhysicalPlaquetteGraphResidualTerminalPredecessorDomination1296
```

Reason: it quantifies over arbitrary `residual essential` with only
`essential subset residual`, which v2.122 showed is too strong.  The corrected
producer must carry residual-fiber provenance from v2.121 bookkeeping or an
equivalent explicit domination hypothesis.

## Non-confusions

This producer is not:

- the v2.124 packing theorem, which only derives the `Fin 1296` injection
  from a bounded explicit menu;
- a raw residual-frontier bound;
- a residual-cardinality bound;
- the local degree bound of one fixed portal or predecessor;
- first-shell or root reachability;
- a post-hoc selection from a current `(X, deleted X)` witness.

The bounded object is the selected terminal-predecessor image produced
residual-locally for the bookkeeping fiber.

## Recommended next task

```text
CODEX-F3-RESIDUAL-FIBER-TERMINAL-PREDECESSOR-DOMINATION-INTERFACE-001
```

Add a no-sorry Lean Prop/interface
`PhysicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296` and,
if safe, the bridge into
`PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296` using the
v2.121 bookkeeping theorem and the v2.124 packing theorem.

## Validation

This was a dashboard-only scope.  No Lean file was edited, so no `lake build`
was required.

## Non-claims

This task does not prove the residual-fiber producer, does not prove
`PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`, does not
compress any decoder alphabet, and does not move `F3-COUNT` out of
`CONDITIONAL_BRIDGE`.  No ledger status, project percentage, README metric,
planner metric, or Clay-level claim moved.
