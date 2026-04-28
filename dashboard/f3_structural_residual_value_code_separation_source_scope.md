# F3 Structural Residual-Value Code Separation Source Scope

Task: `CODEX-F3-SCOPE-STRUCTURAL-RESIDUAL-VALUE-CODE-SEPARATION-SOURCE-001`
Status: `DONE_SCOPE_MINIMAL_FRONTIER_CONFIRMED`
Timestamp: `2026-04-28T08:15:00Z`

## Question

This task scoped whether the v2.234 theorem

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparation1296
```

can honestly reduce to a smaller named theorem, or whether the v2.234
interface is already the minimal current frontier.

The v2.234 data carrier is:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparationData
```

and requires exactly:

- a selector-independent code
  ```lean
  ∀ residual,
    {q : ConcretePlaquette physicalClayDimension L // q ∈ residual} → Fin 1296
  ```
- selected-admissible equality-reflection for any two residual values carrying
  `PhysicalPlaquetteGraphResidualFiberTerminalNeighborSelectorData` evidence
  from essential parents.

## Lean Surface Checked

The relevant Lean definitions are:

- `PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparationData`
- `PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparation1296`
- `physicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296_of_baseZoneResidualValueCodeSeparation1296`
- downstream residual-value interfaces:
  `PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296`,
  `PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296`,
  and `PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296`
- adjacent older coordinate/tag interfaces:
  `PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinate1296`
  and `PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjection1296`

## Result

No Lean theorem was added.  The v2.234 separation theorem is the minimal honest
frontier currently exposed by the Lean API.

The exact no-closure blocker remains:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSeparationData
```

for every residual-fiber instance under the v2.121-style hypotheses.

Any strictly smaller useful theorem would need to construct the same payload
from a genuinely structural residual invariant, not merely rename the v2.234
carrier.  A non-circular source would have to provide:

```text
residualValueCode residual q : Fin 1296
```

for every value in the whole residual subtype, plus a proof that equal codes
reflect equality on the selected-admissible residual values.

## Why Existing Candidates Do Not Reduce It

### Downstream residual-value interfaces

The following interfaces are downstream of v2.234 in the current bridge chain:

```lean
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeRealization1296
PhysicalPlaquetteGraphResidualFiberBaseZoneResidualValueCodeSource1296
PhysicalPlaquetteGraphResidualFiberBaseZoneOriginCertificateCodeInjection1296
```

Using them to prove v2.234 would reverse existing bridge direction and would
make the proof circular.

### Older coordinate/tag carriers

The older carriers

```lean
PhysicalPlaquetteGraphResidualFiberBookkeepingBaseZoneTagCoordinateData
PhysicalPlaquetteGraphResidualFiberSelectorAdmissibleBaseZoneCoordinateInjectionData
```

have fields that resemble the needed code/injectivity payload.  However, the
currently landed Lean bridges send later source/coordinate information into
those carriers; they do not construct v2.234 separation data from the v2.121
residual-fiber hypotheses.  Treating those carriers as the v2.234 source would
skip the missing structural invariant rather than supply it.

## Rejected Routes

This scope did not use and does not authorize:

- selected-image cardinality;
- bounded menu cardinality;
- empirical search;
- `finsetCodeOfCardLe`;
- root-shell, local-neighbor, or local-displacement codes;
- parent-relative `terminalNeighborCode` equality;
- deleted-X shortcuts;
- downstream residual-value source/origin interfaces;
- the v2.161 selector-image cycle.

## Next Repair Task

The next exact Codex task should inventory structural residual invariants that
could non-circularly produce the v2.234 payload:

```text
CODEX-F3-STRUCTURAL-RESIDUAL-VALUE-INVARIANT-INVENTORY-001
```

That task should look for or propose a theorem strictly upstream of v2.234,
such as a residual-local base-zone invariant whose equality implies equality
of selected-admissible residual values and whose range is already `Fin 1296`.
If no such invariant exists, it should record the narrowest missing structural
lemma shape without adding a new axiom or status claim.

## Validation

This is a dashboard-only scope task.  No Lean file was edited, so no
`lake build` was required.

YAML/JSON/JSONL validation passed after registry updates.

F3-COUNT remains `CONDITIONAL_BRIDGE`; no status, percentage, README metric,
planner metric, ledger row, proof closure claim, or Clay-level claim moved.
