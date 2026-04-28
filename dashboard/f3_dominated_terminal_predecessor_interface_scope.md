# F3 dominated terminal-predecessor interface scope v2.123

Task: `CODEX-F3-DOMINATED-TERMINAL-PREDECESSOR-INTERFACE-SCOPE-001`

## Purpose

The v2.122 attempt showed that the current target

```lean
PhysicalPlaquetteGraphResidualTerminalPredecessorDomination1296
```

is too strong as a theorem over arbitrary residual data.  The hypothesis

```lean
essential ⊆ residual
```

does not imply last-edge domination.  A corrected target must either add a
residual-local domination hypothesis or become a packing bridge from explicit
selected terminal-predecessor data.

## Recommended successor interface

Recommended name:

```lean
PhysicalPlaquetteGraphResidualDominatedTerminalPredecessorPacking1296
```

Intended shape:

```lean
def PhysicalPlaquetteGraphResidualDominatedTerminalPredecessorPacking1296 :
    Prop :=
  ∀ {L : ℕ} [NeZero L]
    (residual essential terminalPredMenu :
      Finset (ConcretePlaquette physicalClayDimension L))
    (terminalPredOfParent :
      {p : ConcretePlaquette physicalClayDimension L // p ∈ essential} →
        {q : ConcretePlaquette physicalClayDimension L // q ∈ residual}),
    essential ⊆ residual →
    terminalPredMenu ⊆ residual →
    terminalPredMenu =
      essential.attach.image (fun p => (terminalPredOfParent p).1) →
    (∀ p, (terminalPredOfParent p).1 ∈ terminalPredMenu) →
    (residual.card ≠ 1 →
      ∀ p, p.1 ∈
        (plaquetteGraph physicalClayDimension L).neighborFinset
          (terminalPredOfParent p).1) →
    (∀ p,
      ∃ target : {r : ConcretePlaquette physicalClayDimension L // r ∈ residual},
        target.1 = p.1 ∧
        Nonempty
          (((plaquetteGraph physicalClayDimension L).induce {x | x ∈ residual}).Walk
            (terminalPredOfParent p) target)) →
    terminalPredMenu.card ≤ 1296 →
      ∃ terminalPredCode :
        {q : ConcretePlaquette physicalClayDimension L // q ∈ terminalPredMenu} →
          Fin 1296,
        Function.Injective terminalPredCode
```

This is intentionally a packing/coding theorem.  It does not assert that
last-edge domination follows from arbitrary `essential ⊆ residual`; it takes
the selected residual-local predecessor image and its domination/path evidence
as inputs.

## Alternative stronger producer target

If the project wants a producer rather than a packing bridge, use a separate
target:

```lean
PhysicalPlaquetteGraphResidualFiberTerminalPredecessorDomination1296
```

with additional hypotheses saying that `(residual, essential)` is produced by
the base-aware residual fiber:

```text
essential residual =
  ((plaquetteGraphPreconnectedSubsetsAnchoredCard ... root k).filter
    (fun X => X.erase (deleted X) = residual)).image parentOf
```

together with the v2.116 `hchoice` clauses for `deleted` and `parentOf`.

This route is closer to the current decoder chain, but it is no longer a pure
theorem over arbitrary residual/essential pairs.  It must still keep
terminal-predecessor choices residual-local and cannot choose them post-hoc
from a particular `(X, deleted X)` witness.

## Migration path

The current bridge:

```lean
physicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296_of_baseAwareBookkeeping_of_terminalPredecessorDomination1296
```

uses:

```lean
hterminal :
  PhysicalPlaquetteGraphResidualTerminalPredecessorDomination1296
```

for each `(residual, essential residual)` supplied by
`PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296`.

The corrected chain should split this into two inputs:

1. `PhysicalPlaquetteGraphBaseAwareTerminalPredecessorBookkeeping1296`, already
   proved by v2.121.
2. A new residual-fiber domination producer that supplies
   `terminalPredMenu`, `terminalPredOfParent`, last-edge domination, residual
   path evidence, and `terminalPredMenu.card ≤ 1296` for exactly the essential
   sets arising from the bookkeeping fiber.
3. `PhysicalPlaquetteGraphResidualDominatedTerminalPredecessorPacking1296`,
   which converts the explicit cardinality bound into an injective `Fin 1296`
   code.

Suggested bridge names:

```lean
physicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296_of_baseAwareBookkeeping_of_residualFiberTerminalPredecessorDomination1296

physicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296_of_baseAwareBookkeeping_of_residualFiberDomination_of_terminalPredecessorPacking1296
```

The v2.114 interface should be treated as superseded for proof attempts unless
it is strengthened with explicit domination or fiber-produced hypotheses.

## Non-confusions

The corrected target must not treat any of the following as sufficient for
last-edge domination:

- raw residual frontier size,
- residual cardinality,
- local degree of one fixed portal or predecessor,
- first-shell/root reachability,
- arbitrary `essential ⊆ residual`.

The terminal predecessor menu is the selected image to be bounded.  It is not
the whole raw residual frontier and it is not selected from a current
`(X, deleted X)` witness.

## Recommended next Lean task

```text
CODEX-F3-DOMINATED-TERMINAL-PREDECESSOR-PACKING-INTERFACE-001
```

Add the no-sorry Prop/interface
`PhysicalPlaquetteGraphResidualDominatedTerminalPredecessorPacking1296` and,
if safe, a narrow packing theorem that derives an injective `Fin 1296` code
from `terminalPredMenu.card ≤ 1296`.

## Validation

This was a dashboard-only scope.  No Lean file was edited and no `lake build`
was required by the task.

## Non-claims

This task does not prove:

- `PhysicalPlaquetteGraphResidualTerminalPredecessorDomination1296`,
- `PhysicalPlaquetteGraphResidualLastEdgeDominatingSetBound1296`,
- `PhysicalPlaquetteGraphBaseAwareResidualCanonicalLastEdgePredecessorSelector1296`,
- any decoder compression theorem,
- F3-COUNT closure.

`F3-COUNT` remains `CONDITIONAL_BRIDGE`. No ledger row, project percentage,
README metric, planner metric, or Clay-level claim moved.
