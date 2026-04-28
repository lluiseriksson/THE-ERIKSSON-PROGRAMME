# F3 Terminal-Predecessor Domination Scope v2.113

Task: `CODEX-F3-TERMINAL-PREDECESSOR-DOMINATION-SCOPE-001`

## Purpose

The v2.112 attempt showed that

```lean
PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296
```

is still too bundled for the next proof attempt.  It contains both:

- base-aware deletion and parent bookkeeping over current anchored buckets `X`;
- the genuinely graph-theoretic residual-only terminal-predecessor domination
  burden.

This scope isolates the latter as the next Lean-stable target.

## Proposed Target

Recommended proposition name:

```lean
PhysicalPlaquetteGraphResidualTerminalPredecessorDomination1296
```

Intended shape:

```lean
def PhysicalPlaquetteGraphResidualTerminalPredecessorDomination1296 : Prop :=
  forall {L : Nat} [NeZero L]
    (residual : Finset (ConcretePlaquette physicalClayDimension L))
    (essential : Finset (ConcretePlaquette physicalClayDimension L)),
    essential subset residual ->
    exists terminalPredMenu :
      Finset (ConcretePlaquette physicalClayDimension L),
    exists terminalPredOfParent :
      {p : ConcretePlaquette physicalClayDimension L // p in essential} ->
        {q : ConcretePlaquette physicalClayDimension L // q in residual},
    exists terminalPredCode :
      {q : ConcretePlaquette physicalClayDimension L // q in terminalPredMenu} ->
        Fin 1296,
      terminalPredMenu subset residual /\
      Function.Injective terminalPredCode /\
      terminalPredMenu =
        essential.attach.image (fun p => (terminalPredOfParent p).1) /\
      (forall p, (terminalPredOfParent p).1 in terminalPredMenu) /\
      (residual.card != 1 ->
        forall p,
          p.1 in (plaquetteGraph physicalClayDimension L).neighborFinset
            (terminalPredOfParent p).1) /\
      (forall p,
        exists target : {r : ConcretePlaquette physicalClayDimension L // r in residual},
          target.1 = p.1 /\
          Nonempty
            (((plaquetteGraph physicalClayDimension L).induce {x | x in residual}).Walk
              (terminalPredOfParent p) target))
```

This is intentionally parameterized by `(residual, essential)` and does not
mention a current bucket `X`, a deleted plaquette, or `parentOf`.

## Bridge Target

The exact bridge target is:

```lean
PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296
```

Recommended bridge theorem name:

```lean
physicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296_of_terminalPredecessorDomination1296
```

Bridge idea:

1. use the existing safe-deletion and parent selection clauses required by
   `PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`;
2. define each `essential residual` exactly as the parent image over the
   residual fiber;
3. apply `PhysicalPlaquetteGraphResidualTerminalPredecessorDomination1296` to
   `(residual, essential residual)`;
4. repack the returned `terminalPredMenu`, `terminalPredOfParent`,
   `terminalPredCode`, and induced-walk evidence into v2.111.

The bridge may still need a separate, already expected, proof that
`essential residual ⊆ residual` follows from the base-aware parent choices.
That is bookkeeping, not the selected-image theorem.

## Why This Is Sharper Than v2.111

`PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296` carries deletion
choices:

```lean
deleted : Finset ... -> ConcretePlaquette ...
parentOf : Finset ... -> ConcretePlaquette ...
essential : Finset ... -> Finset ...
```

The proposed target does not.  It only says:

```text
Given residual R and essential parents E subset R,
find a residual-only terminal-predecessor image P subset R,
with |P| <= 1296 encoded by an injective Fin 1296 code,
that last-edge-dominates E.
```

Thus the target isolates the graph-theoretic selected-image burden from the
base-aware deleted-vertex bookkeeping.

## Explicit Non-Confusions

This target bounds selected terminal-predecessor image cardinality.  It does not
bound:

- raw residual frontier growth,
- residual cardinality,
- the local degree of one fixed portal or predecessor,
- first-shell/root reachability from the anchor.

The selected predecessor must be a function of `(residual, essential, p)` data,
not a post-hoc choice from a current `(X, deleted X)` witness.

The v2.109 bounded search is only motivation.  It is not proof evidence.

## Next Task

```text
CODEX-F3-TERMINAL-PREDECESSOR-DOMINATION-INTERFACE-001
```

Add a no-sorry Lean Prop/interface for
`PhysicalPlaquetteGraphResidualTerminalPredecessorDomination1296` and, only if it
builds without `sorry`, the bridge
`physicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296_of_terminalPredecessorDomination1296`.

## Non-Claims

This task does not prove:

- `PhysicalPlaquetteGraphResidualTerminalPredecessorDomination1296`,
- `PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`,
- `PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296`,
- any decoder compression theorem,
- F3-COUNT closure.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No ledger row, project percentage,
README metric, planner metric, or Clay-level claim moved.
